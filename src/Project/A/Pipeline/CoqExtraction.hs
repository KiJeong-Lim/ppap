module Project.A.Pipeline.CoqExtraction where

import Data.List
import System.Directory
import System.Environment
import System.FilePath

import Project.A.Pipeline.Config
import Project.A.Pipeline.ModExtraction
import Project.A.Types
import Project.A.Util.Process
import Z.System
import Z.Utils

data ExtractionOutcome
    = ExtractionOutcome
    { eoTranslatorLog :: Maybe ProcessLog
    , eoCoqcLog :: Maybe ProcessLog
    , eoGhcLog :: Maybe ProcessLog
    , eoRunLog :: Maybe ProcessLog
    , eoExtraLogs :: [(FilePath, ProcessLog)]
    , eoResult :: Either PipelineResult Obs
    } deriving (Eq, Show)

runCoqExtraction :: RunConfig -> FilePath -> RuntimeInput -> IO ExtractionOutcome
runCoqExtraction config caseDir input = do
    translator <- lookupEnv "PROJECT_A_TRANSLATOR"
    case translator of
        Nothing -> return (failedExtraction (TranslatorError missingTranslatorMessage))
        Just commandLine -> runConfiguredTranslator config caseDir input commandLine

missingTranslatorMessage :: String
missingTranslatorMessage = "PROJECT_A_TRANSLATOR is not set. Set it to a command that reads gofile.go and writes generated Coq to stdout."

runConfiguredTranslator :: RunConfig -> FilePath -> RuntimeInput -> String -> IO ExtractionOutcome
runConfiguredTranslator config caseDir input commandLine
    = case words commandLine of
        [] -> return (failedExtraction (TranslatorError missingTranslatorMessage))
        command : baseArgs -> do
            let timeouts = cfgTimeouts config
            translatorResult <- runTimedProcess (timeoutTranslator timeouts) (Just caseDir) [] command (baseArgs ++ ["gofile.go"]) ""
            let translatorLog = processLog translatorResult
            if not (processSucceeded translatorResult) then
                return (failedAfterTranslator translatorLog (TranslatorError (plStderr translatorLog ++ plStdout translatorLog)))
            else do
                _ <- writeFileNow (caseDir </> "coq" </> "gofile.v") (tprStdout translatorResult)
                mode <- lookupEnv "PROJECT_A_EXTRACT_MODE"
                case mode of
                    Just "mod" -> runModExtractionAndHaskell config caseDir input translatorLog
                    _ -> runCoqcAndHaskell config caseDir input translatorLog

runCoqcAndHaskell :: RunConfig -> FilePath -> RuntimeInput -> ProcessLog -> IO ExtractionOutcome
runCoqcAndHaskell config caseDir input translatorLog
    = do
        let timeouts = cfgTimeouts config
        coqcResult <- runTimedProcess (timeoutCoqc timeouts) (Just caseDir) [] "coqc" ["coq" </> "gofile.v"] ""
        let coqcLog = processLog coqcResult
        if not (processSucceeded coqcResult) then
            return (failedAfterCoqc translatorLog coqcLog (CoqError coqcLog))
        else do
            let hsFile = caseDir </> "coq" </> "extracted" </> "Gofile.hs"
            hsExists <- doesFileExist hsFile
            if not hsExists then
                return (failedAfterCoqc translatorLog coqcLog (ExtractionError ("Expected extracted file does not exist: " ++ hsFile)))
            else do
                ghcExtraArgs <- ghcExtraArgsFromEnv
                ghcResult <- runTimedProcess (timeoutGhc timeouts) (Just caseDir) [] "ghc" (ghcArgs ghcExtraArgs) ""
                let ghcLog = processLog ghcResult
                if not (processSucceeded ghcResult) then
                    return (failedAfterGhc translatorLog coqcLog ghcLog (HaskellCompileError ghcLog))
                else do
                    runResult <- runTimedProcess (timeoutExtractedRun timeouts) (Just caseDir) (riEnv input) ("." </> "coq" </> "extracted" </> "gofile-hs") (riArgs input) (riStdin input)
                    return ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Just (processLog runResult), eoExtraLogs = [], eoResult = Right (obsFromProcess runResult) }
    where
        ghcArgs :: [String] -> [String]
        ghcArgs extraArgs = extraArgs ++ ["-outputdir", "coq" </> "extracted", "-odir", "coq" </> "extracted", "-hidir", "coq" </> "extracted", "coq" </> "extracted" </> "Gofile.hs", "-o", "coq" </> "extracted" </> "gofile-hs"]

runModExtractionAndHaskell :: RunConfig -> FilePath -> RuntimeInput -> ProcessLog -> IO ExtractionOutcome
runModExtractionAndHaskell config caseDir input translatorLog = do
    extractConfig <- modExtractConfigFromEnv (caseDir </> "coq" </> "gofile.v")
    report <- runModExtraction config { cfgWorkDir = caseDir </> "coq" } extractConfig
    let coqcLog = merHarnessLog report
        extraLogs = modExtractionLogs report
    case merResult report of
        Left err
            | plExitCode coqcLog /= Just 0 -> return (failedAfterCoqcExtra translatorLog coqcLog extraLogs (CoqError coqcLog))
            | otherwise -> return (failedAfterCoqcExtra translatorLog coqcLog extraLogs (ExtractionError err))
        Right hsFile -> runExtractedHaskell config caseDir input translatorLog coqcLog extraLogs hsFile

runExtractedHaskell :: RunConfig -> FilePath -> RuntimeInput -> ProcessLog -> ProcessLog -> [(FilePath, ProcessLog)] -> FilePath -> IO ExtractionOutcome
runExtractedHaskell config caseDir input translatorLog coqcLog extraLogs hsFile
    = do
        let timeouts = cfgTimeouts config
        driverFile <- writeModHaskellDriver hsFile
        ghcExtraArgs <- ghcExtraArgsFromEnv
        ghcResult <- runTimedProcess (timeoutGhc timeouts) (Just caseDir) [] "ghc" (ghcArgs ghcExtraArgs driverFile) ""
        let ghcLog = processLog ghcResult
        if not (processSucceeded ghcResult) then
            return (failedAfterGhcExtra translatorLog coqcLog ghcLog extraLogs (HaskellCompileError ghcLog))
        else do
            runResult <- runTimedProcess (timeoutExtractedRun timeouts) (Just caseDir) (riEnv input) ("." </> "coq" </> "extracted" </> "gofile-hs") (riArgs input) (riStdin input)
            return ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Just (processLog runResult), eoExtraLogs = extraLogs, eoResult = Right (obsFromProcess runResult) }
    where
        ghcArgs extraArgs driverFile = ["-XNoPolyKinds"] ++ extraArgs ++ ["-i" ++ takeDirectory driverFile, "-outputdir", "coq" </> "extracted", "-odir", "coq" </> "extracted", "-hidir", "coq" </> "extracted", driverFile, "-o", "coq" </> "extracted" </> "gofile-hs"]

ghcExtraArgsFromEnv :: IO [String]
ghcExtraArgsFromEnv = envList "PROJECT_A_GHC_ARGS" []

writeModHaskellDriver :: FilePath -> IO FilePath
writeModHaskellDriver hsFile = do
    let driverFile = takeDirectory hsFile </> "Main.hs"
    extractedText <- maybe (fail ("cannot read file: " ++ hsFile)) return =<< readFileNow hsFile
    _ <- writeFileNow driverFile (modHaskellDriverText (extractedBackendShape extractedText) (takeBaseName hsFile))
    return driverFile

data BackendArgShape
    = NoBackendValues
    | UntypedBackendValues BackendNames
    | ExprBackendValues BackendNames ExprBackendNames
    deriving (Eq, Ord, Show)

data BackendNames
    = BackendNames
    deriving (Eq, Ord, Show)

data ExprBackendNames
    = ExprBackendNames
    { ebExprType :: String
    , ebTypeType :: String
    , ebTintCtor :: String
    , ebTboolCtor :: String
    , ebSignedCtor :: String
    , ebUnsignedCtor :: String
    } deriving (Eq, Ord, Show)

extractedBackendShape :: String -> BackendArgShape
extractedBackendShape extractedText
    = case extractedBackendNames extractedText of
        Nothing -> NoBackendValues
        Just backendNames ->
            case extractedExprBackendNames extractedText of
                Just exprNames -> ExprBackendValues backendNames exprNames
                Nothing -> UntypedBackendValues backendNames

extractedBackendNames :: String -> Maybe BackendNames
extractedBackendNames extractedText
    | not (all (`isInfixOf` extractedText) ["data Val", "Vint", "Vlong"]) = Nothing
    | otherwise = Just BackendNames

extractedExprBackendNames :: String -> Maybe ExprBackendNames
extractedExprBackendNames extractedText = do
    (exprType, elitLine) <- dataBlockWithConstructor extractedText "Elit"
    typeType <- lastMaybe (constructorWords elitLine)
    tintLine <- constructorLine extractedText typeType "Tint"
    let tintWords = constructorWords tintLine
    tintCtor <- headMaybe tintWords
    signednessType <- headMaybe (drop 2 tintWords)
    tboolCtor <- constructorNameWithPrefix extractedText typeType "Tbool"
    signedCtor <- constructorNameWithPrefix extractedText signednessType "Signed"
    unsignedCtor <- constructorNameWithPrefix extractedText signednessType "Unsigned"
    return ExprBackendNames
        { ebExprType = exprType
        , ebTypeType = typeType
        , ebTintCtor = tintCtor
        , ebTboolCtor = tboolCtor
        , ebSignedCtor = signedCtor
        , ebUnsignedCtor = unsignedCtor
        }

constructorNameWithPrefix :: String -> String -> String -> Maybe String
constructorNameWithPrefix extractedText typeName ctorPrefix = headMaybe . constructorWords =<< constructorLine extractedText typeName ctorPrefix

constructorLine :: String -> String -> String -> Maybe String
constructorLine extractedText typeName ctorPrefix
    = find (constructorStartsWith ctorPrefix) (dataBlock extractedText typeName)

dataBlockWithConstructor :: String -> String -> Maybe (String, String)
dataBlockWithConstructor extractedText ctorPrefix = go (lines extractedText) where
    go [] = Nothing
    go (line : rest)
        | Just typeName <- dataTypeName line
        = case find (constructorStartsWith ctorPrefix) (takeDataBlock rest) of
            Just ctorLine -> Just (typeName, ctorLine)
            Nothing -> go rest
        | otherwise = go rest

dataBlock :: String -> String -> [String]
dataBlock extractedText typeName
    = case dropWhile (not . isDataLine typeName) (lines extractedText) of
        [] -> []
        _ : rest -> takeDataBlock rest

takeDataBlock :: [String] -> [String]
takeDataBlock = takeWhile (not . startsTopLevelDecl)

startsTopLevelDecl :: String -> Bool
startsTopLevelDecl line
    = any (`isPrefixOf` trimLeft line) ["data ", "type ", "newtype ", "class ", "instance "]

isDataLine :: String -> String -> Bool
isDataLine typeName line = ("data " ++ typeName ++ " =") `isPrefixOf` trimLeft line

dataTypeName :: String -> Maybe String
dataTypeName line
    = case words (trimLeft line) of
        "data" : typeName : "=" : _ -> Just typeName
        _ -> Nothing

constructorStartsWith :: String -> String -> Bool
constructorStartsWith ctorPrefix line
    = case headMaybe (constructorWords line) of
        Just ctor -> ctorPrefix `isPrefixOf` ctor
        Nothing -> False

constructorWords :: String -> [String]
constructorWords line
    = case words (trimLeft line) of
        "|" : rest -> rest
        words' -> words'

trimLeft :: String -> String
trimLeft = dropWhile (== ' ')

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x : _) = Just x

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just (last xs)

modHaskellDriverText :: BackendArgShape -> String -> String
modHaskellDriverText backendShape extractedModule = modHaskellDriverText' backendShape extractedModule ""

modHaskellDriverText' :: BackendArgShape -> String -> ShowS
modHaskellDriverText' backendShape extractedModule = strcat
    [ strstr "module Main where" . nl
    , nl
    , strstr "import qualified Data.Char as Char" . nl
    , strstr "import qualified Prelude" . nl
    , strstr "import qualified " . strstr extractedModule . strstr " as Extracted" . nl
    , nl
    , strstr "main :: Prelude.IO ()" . nl
    , strstr "main = do" . nl
    , strstr "    stdinText <- Prelude.getContents" . nl
    , strstr "    run (Prelude.words stdinText) Extracted.project_a_target_itr" . nl
    , nl
    , strstr "type ScanState = [Prelude.String]" . nl
    , nl
    , strstr "run :: ScanState -> Extracted.Itree (Extracted.CoreE Extracted.Any) Extracted.T0 -> Prelude.IO ()" . nl
    , strstr "run scanState itr =" . nl
    , strstr "    case Extracted.observe itr of" . nl
    , strstr "        Extracted.RetF _ -> Prelude.return ()" . nl
    , strstr "        Extracted.TauF next -> run scanState next" . nl
    , strstr "        Extracted.VisF event kont -> do" . nl
    , strstr "            (value, scanState') <- handleCoreEvent scanState event" . nl
    , strstr "            run scanState' (kont value)" . nl
    , nl
    , strstr "handleCoreEvent :: ScanState -> Extracted.CoreE Extracted.Any -> Prelude.IO (Extracted.Any, ScanState)" . nl
    , strstr "handleCoreEvent scanState Extracted.Choose = Prelude.return (chooseValue, scanState)" . nl
    , strstr "handleCoreEvent scanState Extracted.Take = Prelude.return (takeValue, scanState)" . nl
    , strstr "handleCoreEvent scanState (Extracted.IO name args) = handleExternalIO scanState (coqStringToString name) args" . nl
    , nl
    , strstr "chooseValue :: Extracted.Any" . nl
    , strstr "chooseValue = Extracted.unsafeCoerce Extracted.O" . nl
    , nl
    , strstr "takeValue :: Extracted.Any" . nl
    , strstr "takeValue = Extracted.unsafeCoerce ()" . nl
    , nl
    , strstr "ioValue :: Extracted.Any" . nl
    , strstr "ioValue = Extracted.unsafeCoerce ([] :: [()])" . nl
    , nl
    , strstr "handleExternalIO :: ScanState -> Prelude.String -> Extracted.Any -> Prelude.IO (Extracted.Any, ScanState)" . nl
    , strstr "handleExternalIO scanState name args" . nl
    , strstr "    | name Prelude.== \"project-a.stdout\" = printExactStdout args Prelude.>> Prelude.return (ioValue, scanState)" . nl
    , strstr "    | name Prelude.== \"project-a.stdout-line\" = printExactStdout args Prelude.>> Prelude.putChar '\\n' Prelude.>> Prelude.return (ioValue, scanState)" . nl
    , backendIODriverText backendShape
    , nl
    , strstr "printExactStdout :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printExactStdout args = Prelude.putStr (Prelude.concat (Prelude.map coqStringToString (Extracted.unsafeCoerce args :: [Extracted.String])))" . nl
    , nl
    , strstr "coqStringToString :: Extracted.String -> Prelude.String" . nl
    , strstr "coqStringToString Extracted.EmptyString = []" . nl
    , strstr "coqStringToString (Extracted.String0 ch rest) = asciiToChar ch : coqStringToString rest" . nl
    , nl
    , strstr "asciiToChar :: Extracted.Ascii0 -> Prelude.Char" . nl
    , strstr "asciiToChar (Extracted.Ascii b0 b1 b2 b3 b4 b5 b6 b7) = Char.chr (bit 0 b0 Prelude.+ bit 1 b1 Prelude.+ bit 2 b2 Prelude.+ bit 3 b3 Prelude.+ bit 4 b4 Prelude.+ bit 5 b5 Prelude.+ bit 6 b6 Prelude.+ bit 7 b7)" . nl
    , nl
    , strstr "bit :: Prelude.Int -> Prelude.Bool -> Prelude.Int" . nl
    , strstr "bit n flag = if flag then 2 Prelude.^ n else 0" . nl
    ]

backendIODriverText :: BackendArgShape -> ShowS
backendIODriverText NoBackendValues = strstr "    | Prelude.otherwise = Prelude.return (ioValue, scanState)" . nl
backendIODriverText (UntypedBackendValues backendNames) = backendIODriverBody backendNames (untypedBackendArgText backendNames)
backendIODriverText (ExprBackendValues backendNames exprNames) = backendIODriverBody backendNames (exprBackendArgText backendNames exprNames)

backendIODriverBody :: BackendNames -> ShowS -> ShowS
backendIODriverBody backendNames argText = strcat
    [ strstr "    | name Prelude.== \"Go.builtin.scan\" = scanBackendValues scanState args" . nl
    , strstr "    | name Prelude.== \"Go.builtin.print\" = printBackendValuesNoNewline args Prelude.>> Prelude.return (ioValue, scanState)" . nl
    , strstr "    | name Prelude.== \"fmt.Println\" = printBackendValues args Prelude.>> Prelude.return (ioValue, scanState)" . nl
    , strstr "    | name Prelude.== \"fmt.Print\" = printBackendValuesNoNewline args Prelude.>> Prelude.return (ioValue, scanState)" . nl
    , strstr "    | Prelude.otherwise = Prelude.return (ioValue, scanState)" . nl
    , nl
    , argText
    , backendValueText backendNames
    ]

untypedBackendArgText :: BackendNames -> ShowS
untypedBackendArgText _ = strcat
    [ strstr "printBackendValues :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValues args = Prelude.putStrLn (joinWords (Prelude.map renderBackendValue (Extracted.unsafeCoerce args :: [Extracted.Val])))" . nl
    , nl
    , strstr "printBackendValuesNoNewline :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValuesNoNewline args = Prelude.putStr (joinWords (Prelude.map renderBackendValue (Extracted.unsafeCoerce args :: [Extracted.Val])))" . nl
    , nl
    , strstr "scanBackendValues :: ScanState -> Extracted.Any -> Prelude.IO (Extracted.Any, ScanState)" . nl
    , strstr "scanBackendValues scanState args =" . nl
    , strstr "    let targetCount = Prelude.length (Extracted.unsafeCoerce args :: [Extracted.Val])" . nl
    , strstr "        (usedTokens, remainingTokens) = Prelude.splitAt targetCount scanState" . nl
    , strstr "        paddedTokens = usedTokens Prelude.++ Prelude.replicate (targetCount Prelude.- Prelude.length usedTokens) \"0\"" . nl
    , strstr "        scannedValues = Prelude.map parseBackendInt paddedTokens" . nl
    , strstr "    in Prelude.return (Extracted.unsafeCoerce (scannedValues :: [Extracted.Val]), remainingTokens)" . nl
    , nl
    ]

exprBackendArgText :: BackendNames -> ExprBackendNames -> ShowS
exprBackendArgText _ exprNames = strcat
    [ strstr "type BackendArg = (Extracted." . strstr (ebExprType exprNames) . strstr ", Extracted.Val)" . nl
    , nl
    , strstr "printBackendValues :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValues args = Prelude.putStrLn (joinWords (Prelude.map renderBackendArg (Extracted.unsafeCoerce args :: [BackendArg])))" . nl
    , nl
    , strstr "printBackendValuesNoNewline :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValuesNoNewline args = Prelude.putStr (joinWords (Prelude.map renderBackendArg (Extracted.unsafeCoerce args :: [BackendArg])))" . nl
    , nl
    , strstr "scanBackendValues :: ScanState -> Extracted.Any -> Prelude.IO (Extracted.Any, ScanState)" . nl
    , strstr "scanBackendValues scanState args =" . nl
    , strstr "    let targetCount = Prelude.length (Extracted.unsafeCoerce args :: [BackendArg])" . nl
    , strstr "        (usedTokens, remainingTokens) = Prelude.splitAt targetCount scanState" . nl
    , strstr "        paddedTokens = usedTokens Prelude.++ Prelude.replicate (targetCount Prelude.- Prelude.length usedTokens) \"0\"" . nl
    , strstr "        scannedValues = Prelude.map parseBackendInt paddedTokens" . nl
    , strstr "    in Prelude.return (Extracted.unsafeCoerce (scannedValues :: [Extracted.Val]), remainingTokens)" . nl
    , nl
    , strstr "renderBackendArg :: BackendArg -> Prelude.String" . nl
    , strstr "renderBackendArg (expr, value) = renderBackendValueAs (exprType expr) value" . nl
    , nl
    , strstr "exprType :: Extracted." . strstr (ebExprType exprNames) . strstr " -> Extracted." . strstr (ebTypeType exprNames) . nl
    , strstr "exprType expr =" . nl
    , strstr "    case expr of" . nl
    , strstr "        Extracted.Elit _ ty -> ty" . nl
    , strstr "        Extracted.Evar _ ty -> ty" . nl
    , strstr "        Extracted.Ederef _ ty -> ty" . nl
    , strstr "        Extracted.Eaddrof _ ty -> ty" . nl
    , strstr "        Extracted.Eunop _ _ ty -> ty" . nl
    , strstr "        Extracted.Ebinop _ _ _ ty -> ty" . nl
    , strstr "        Extracted.Ecast _ _ ty -> ty" . nl
    , strstr "        Extracted.Efield _ _ ty -> ty" . nl
    , strstr "        Extracted.Eindexop _ _ ty -> ty" . nl
    , strstr "        Extracted.Esliceop _ _ _ ty -> ty" . nl
    , nl
    , strstr "renderBackendValueAs :: Extracted." . strstr (ebTypeType exprNames) . strstr " -> Extracted.Val -> Prelude.String" . nl
    , strstr "renderBackendValueAs (Extracted." . strstr (ebTintCtor exprNames) . strstr " _ Extracted." . strstr (ebSignedCtor exprNames) . strstr ") (Extracted.Vint n) = Prelude.show (signedInteger 32 n)" . nl
    , strstr "renderBackendValueAs (Extracted." . strstr (ebTintCtor exprNames) . strstr " _ Extracted." . strstr (ebUnsignedCtor exprNames) . strstr ") (Extracted.Vint n) = Prelude.show (unsignedInteger 32 n)" . nl
    , strstr "renderBackendValueAs (Extracted." . strstr (ebTintCtor exprNames) . strstr " _ Extracted." . strstr (ebSignedCtor exprNames) . strstr ") (Extracted.Vlong n) = Prelude.show (signedInteger 64 n)" . nl
    , strstr "renderBackendValueAs (Extracted." . strstr (ebTintCtor exprNames) . strstr " _ Extracted." . strstr (ebUnsignedCtor exprNames) . strstr ") (Extracted.Vlong n) = Prelude.show (unsignedInteger 64 n)" . nl
    , strstr "renderBackendValueAs Extracted." . strstr (ebTboolCtor exprNames) . strstr " (Extracted.Vint n) = if unsignedInteger 32 n Prelude.== 0 then \"false\" else \"true\"" . nl
    , strstr "renderBackendValueAs _ value = renderBackendValue value" . nl
    , nl
    ]

backendValueText :: BackendNames -> ShowS
backendValueText _ = strcat
    [ strstr "parseBackendInt :: Prelude.String -> Extracted.Val" . nl
    , strstr "parseBackendInt token = backendIntValue (parseIntegerToken token)" . nl
    , nl
    , strstr "parseIntegerToken :: Prelude.String -> Prelude.Integer" . nl
    , strstr "parseIntegerToken token =" . nl
    , strstr "    case (Prelude.reads token :: [(Prelude.Integer, Prelude.String)]) of" . nl
    , strstr "        [(n, \"\")] -> n" . nl
    , strstr "        _ -> 0" . nl
    , nl
    , strstr "backendIntValue :: Prelude.Integer -> Extracted.Val" . nl
    , strstr "backendIntValue n =" . nl
    , strstr "    if Extracted.ptr64" . nl
    , strstr "        then Extracted.Vlong (integerToZ (unsignedModulo 64 n))" . nl
    , strstr "        else Extracted.Vint (integerToZ (unsignedModulo 32 n))" . nl
    , nl
    , strstr "renderBackendValue :: Extracted.Val -> Prelude.String" . nl
    , strstr "renderBackendValue Extracted.Vundef = \"<undef>\"" . nl
    , strstr "renderBackendValue (Extracted.Vint n) = Prelude.show (signedInteger 32 n)" . nl
    , strstr "renderBackendValue (Extracted.Vlong n) = Prelude.show (signedInteger 64 n)" . nl
    , strstr "renderBackendValue (Extracted.Vfloat _) = \"<float>\"" . nl
    , strstr "renderBackendValue (Extracted.Vsingle _) = \"<float>\"" . nl
    , strstr "renderBackendValue (Extracted.Vptr _ _) = \"<ptr>\"" . nl
    , nl
    , strstr "joinWords :: [Prelude.String] -> Prelude.String" . nl
    , strstr "joinWords [] = \"\"" . nl
    , strstr "joinWords [x] = x" . nl
    , strstr "joinWords (x : xs) = x Prelude.++ Prelude.concatMap (\" \" Prelude.++) xs" . nl
    , nl
    , strstr "signedInteger :: Prelude.Integer -> Extracted.Z -> Prelude.Integer" . nl
    , strstr "signedInteger bits z =" . nl
    , strstr "    let x = unsignedInteger bits z" . nl
    , strstr "        half = 2 Prelude.^ (bits Prelude.- 1)" . nl
    , strstr "        modulus = 2 Prelude.^ bits" . nl
    , strstr "    in if x Prelude.< half then x else x Prelude.- modulus" . nl
    , nl
    , strstr "unsignedInteger :: Prelude.Integer -> Extracted.Z -> Prelude.Integer" . nl
    , strstr "unsignedInteger bits z = unsignedModulo bits (zToInteger z)" . nl
    , nl
    , strstr "unsignedModulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer" . nl
    , strstr "unsignedModulo bits n = n `Prelude.mod` (2 Prelude.^ bits)" . nl
    , nl
    , strstr "zToInteger :: Extracted.Z -> Prelude.Integer" . nl
    , strstr "zToInteger Extracted.Z0 = 0" . nl
    , strstr "zToInteger (Extracted.Zpos p) = positiveToInteger p" . nl
    , strstr "zToInteger (Extracted.Zneg p) = Prelude.negate (positiveToInteger p)" . nl
    , nl
    , strstr "positiveToInteger :: Extracted.Positive -> Prelude.Integer" . nl
    , strstr "positiveToInteger Extracted.XH = 1" . nl
    , strstr "positiveToInteger (Extracted.XO p) = 2 Prelude.* positiveToInteger p" . nl
    , strstr "positiveToInteger (Extracted.XI p) = 1 Prelude.+ 2 Prelude.* positiveToInteger p" . nl
    , nl
    , strstr "integerToZ :: Prelude.Integer -> Extracted.Z" . nl
    , strstr "integerToZ n" . nl
    , strstr "    | n Prelude.== 0 = Extracted.Z0" . nl
    , strstr "    | n Prelude.> 0 = Extracted.Zpos (positiveFromInteger n)" . nl
    , strstr "    | Prelude.otherwise = Extracted.Zneg (positiveFromInteger (Prelude.negate n))" . nl
    , nl
    , strstr "positiveFromInteger :: Prelude.Integer -> Extracted.Positive" . nl
    , strstr "positiveFromInteger n" . nl
    , strstr "    | n Prelude.<= 1 = Extracted.XH" . nl
    , strstr "    | n `Prelude.mod` 2 Prelude.== 0 = Extracted.XO (positiveFromInteger (n `Prelude.div` 2))" . nl
    , strstr "    | Prelude.otherwise = Extracted.XI (positiveFromInteger (n `Prelude.div` 2))" . nl
    ]

modExtractionLogs :: ModExtractReport -> [(FilePath, ProcessLog)]
modExtractionLogs report = concat
    [ maybe [] (\logValue -> [("mod-extract-opam-env.log", logValue)]) (merOpamEnvLog report)
    , maybe [] (\logValue -> [("mod-extract-input.log", logValue)]) (merInputLog report)
    ]

modExtractConfigFromEnv :: FilePath -> IO ModExtractConfig
modExtractConfigFromEnv coqFile = do
    toolRoot <- lookupEnv "PROJECT_A_TOOL_ROOT"
    backendRootEnv <- lookupEnv "PROJECT_A_BACKEND_ROOT"
    opamEnvDirEnv <- lookupEnv "PROJECT_A_OPAM_ENV_DIR"
    coqProjectFilesEnv <- lookupEnv "PROJECT_A_COQPROJECTS"
    coqcCommand <- envString "PROJECT_A_COQC" (mecCoqcCommand defaultModExtractConfig)
    coqExtraArgs <- envList "PROJECT_A_COQ_ARGS" (mecCoqExtraArgs defaultModExtractConfig)
    backendLogical <- envString "PROJECT_A_BACKEND_LOGICAL" (mecBackendLogical defaultModExtractConfig)
    backendLoadDirs <- envList "PROJECT_A_BACKEND_DIRS" (mecBackendLoadDirs defaultModExtractConfig)
    projectLogical <- envString "PROJECT_A_PROJECT_LOGICAL" (mecProjectLogical defaultModExtractConfig)
    coreRequires <- envList "PROJECT_A_BACKEND_CORE_REQUIRE" (mecCoreRequireModules defaultModExtractConfig)
    extractionLanguage <- envString "PROJECT_A_EXTRACTION_LANGUAGE" (mecExtractionLanguage defaultModExtractConfig)
    extractionSupport <- envString "PROJECT_A_EXTRACTION_SUPPORT" (mecExtractionSupportModule defaultModExtractConfig)
    extractionBlacklist <- envList "PROJECT_A_EXTRACTION_BLACKLIST" (mecExtractionBlacklist defaultModExtractConfig)
    graTerm <- envString "PROJECT_A_BACKEND_GRA" (mecGraTerm defaultModExtractConfig)
    requires <- envList "PROJECT_A_EXTRACT_REQUIRE" (mecRequireModules defaultModExtractConfig)
    modTerm <- envString "PROJECT_A_EXTRACT_MOD" "Input.t"
    resourceTerm <- envString "PROJECT_A_EXTRACT_RESOURCE" (mecResourceTerm defaultModExtractConfig)
    argTerm <- envString "PROJECT_A_EXTRACT_ARG" (mecArgTerm defaultModExtractConfig)
    outputFile <- envString "PROJECT_A_EXTRACT_OUTPUT" (mecOutputFile defaultModExtractConfig)
    let backendRoot = maybe (deriveBackendRoot toolRoot (mecBackendRoot defaultModExtractConfig)) id backendRootEnv
        opamEnvDir = case opamEnvDirEnv of
            Just dir -> Just dir
            Nothing -> toolRoot
        coqProjectFiles = case coqProjectFilesEnv of
            Just str -> commaWords str
            Nothing -> maybe [] (\root -> [root </> "_CoqProject"]) toolRoot
    return defaultModExtractConfig
        { mecBackendRoot = backendRoot
        , mecToolRoot = toolRoot
        , mecCoqcCommand = coqcCommand
        , mecOpamEnvDir = opamEnvDir
        , mecCoqExtraArgs = coqExtraArgs
        , mecCoqProjectFiles = coqProjectFiles
        , mecBackendLogical = backendLogical
        , mecBackendLoadDirs = backendLoadDirs
        , mecProjectLogical = projectLogical
        , mecCoreRequireModules = coreRequires
        , mecExtractionLanguage = extractionLanguage
        , mecExtractionSupportModule = extractionSupport
        , mecExtractionBlacklist = extractionBlacklist
        , mecGraTerm = graTerm
        , mecCoqFile = Just coqFile
        , mecRequireModules = requires
        , mecModTerm = modTerm
        , mecResourceTerm = resourceTerm
        , mecArgTerm = argTerm
        , mecOutputFile = outputFile
        }

deriveBackendRoot :: Maybe FilePath -> FilePath -> FilePath
deriveBackendRoot Nothing backendRoot = backendRoot
deriveBackendRoot (Just toolRoot) backendRoot
    | backendRoot == mecBackendRoot defaultModExtractConfig = toolRoot </> "__PROJECT_A_BOOT_STACK_DIR__" </> "__PROJECT_A_BOOT_BACKEND_DIR__"
    | otherwise = backendRoot

envString :: String -> String -> IO String
envString key fallback = maybe fallback id <$> lookupEnv key

envList :: String -> [String] -> IO [String]
envList key fallback = maybe fallback commaWords <$> lookupEnv key

commaWords :: String -> [String]
commaWords "" = []
commaWords str = filter (not . null) (map trim (splitComma str))

splitComma :: String -> [String]
splitComma str
    = case break (== ',') str of
        (word, "") -> [word]
        (word, _ : rest) -> word : splitComma rest

trim :: String -> String
trim = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

failedExtraction :: PipelineResult -> ExtractionOutcome
failedExtraction result = ExtractionOutcome { eoTranslatorLog = Nothing, eoCoqcLog = Nothing, eoGhcLog = Nothing, eoRunLog = Nothing, eoExtraLogs = [], eoResult = Left result }

failedAfterTranslator :: ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterTranslator translatorLog result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Nothing, eoGhcLog = Nothing, eoRunLog = Nothing, eoExtraLogs = [], eoResult = Left result }

failedAfterCoqc :: ProcessLog -> ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterCoqc translatorLog coqcLog result = failedAfterCoqcExtra translatorLog coqcLog [] result

failedAfterCoqcExtra :: ProcessLog -> ProcessLog -> [(FilePath, ProcessLog)] -> PipelineResult -> ExtractionOutcome
failedAfterCoqcExtra translatorLog coqcLog extraLogs result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Nothing, eoRunLog = Nothing, eoExtraLogs = extraLogs, eoResult = Left result }

failedAfterGhc :: ProcessLog -> ProcessLog -> ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterGhc translatorLog coqcLog ghcLog result = failedAfterGhcExtra translatorLog coqcLog ghcLog [] result

failedAfterGhcExtra :: ProcessLog -> ProcessLog -> ProcessLog -> [(FilePath, ProcessLog)] -> PipelineResult -> ExtractionOutcome
failedAfterGhcExtra translatorLog coqcLog ghcLog extraLogs result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Nothing, eoExtraLogs = extraLogs, eoResult = Left result }
