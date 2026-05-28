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
    _ <- writeFileNow driverFile (modHaskellDriverText (extractedHasBackendValues extractedText) (takeBaseName hsFile))
    return driverFile

extractedHasBackendValues :: String -> Bool
extractedHasBackendValues extractedText = all (`isInfixOf` extractedText) ["data Val", "Vint", "Vlong", "signed0"]

modHaskellDriverText :: Bool -> String -> String
modHaskellDriverText hasBackendValues extractedModule = modHaskellDriverText' hasBackendValues extractedModule ""

modHaskellDriverText' :: Bool -> String -> ShowS
modHaskellDriverText' hasBackendValues extractedModule = strcat
    [ strstr "module Main where" . nl
    , nl
    , strstr "import qualified Data.Char as Char" . nl
    , strstr "import qualified Prelude" . nl
    , strstr "import qualified " . strstr extractedModule . strstr " as Extracted" . nl
    , nl
    , strstr "main :: Prelude.IO ()" . nl
    , strstr "main = run Extracted.project_a_target_itr" . nl
    , nl
    , strstr "run :: Extracted.Itree (Extracted.CoreE Extracted.Any) Extracted.T0 -> Prelude.IO ()" . nl
    , strstr "run itr =" . nl
    , strstr "    case Extracted.observe itr of" . nl
    , strstr "        Extracted.RetF _ -> Prelude.return ()" . nl
    , strstr "        Extracted.TauF next -> run next" . nl
    , strstr "        Extracted.VisF event kont -> handleCoreEvent event Prelude.>>= run Prelude.. kont" . nl
    , nl
    , strstr "handleCoreEvent :: Extracted.CoreE Extracted.Any -> Prelude.IO Extracted.Any" . nl
    , strstr "handleCoreEvent Extracted.Choose = Prelude.return chooseValue" . nl
    , strstr "handleCoreEvent Extracted.Take = Prelude.return takeValue" . nl
    , strstr "handleCoreEvent (Extracted.IO name args) = handleExternalIO (coqStringToString name) args Prelude.>> Prelude.return ioValue" . nl
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
    , strstr "handleExternalIO :: Prelude.String -> Extracted.Any -> Prelude.IO ()" . nl
    , strstr "handleExternalIO name args" . nl
    , strstr "    | name Prelude.== \"project-a.stdout\" = printExactStdout args" . nl
    , strstr "    | name Prelude.== \"project-a.stdout-line\" = printExactStdout args Prelude.>> Prelude.putChar '\\n'" . nl
    , if hasBackendValues then backendPrintDriverText else strstr "    | Prelude.otherwise = Prelude.return ()" . nl
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

backendPrintDriverText :: ShowS
backendPrintDriverText = strcat
    [ strstr "    | name Prelude.== \"Go.builtin.print\" = printBackendValues args" . nl
    , strstr "    | name Prelude.== \"fmt.Println\" = printBackendValues args" . nl
    , strstr "    | name Prelude.== \"fmt.Print\" = printBackendValuesNoNewline args" . nl
    , strstr "    | Prelude.otherwise = Prelude.return ()" . nl
    , nl
    , strstr "printBackendValues :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValues args = Prelude.putStrLn (joinWords (Prelude.map renderBackendValue (Extracted.unsafeCoerce args :: [Extracted.Val])))" . nl
    , nl
    , strstr "printBackendValuesNoNewline :: Extracted.Any -> Prelude.IO ()" . nl
    , strstr "printBackendValuesNoNewline args = Prelude.putStr (joinWords (Prelude.map renderBackendValue (Extracted.unsafeCoerce args :: [Extracted.Val])))" . nl
    , nl
    , strstr "renderBackendValue :: Extracted.Val -> Prelude.String" . nl
    , strstr "renderBackendValue Extracted.Vundef = \"<undef>\"" . nl
    , strstr "renderBackendValue (Extracted.Vint n) = Prelude.show (zToInteger (Extracted.signed0 n))" . nl
    , strstr "renderBackendValue (Extracted.Vlong n) = Prelude.show (zToInteger (Extracted.signed n))" . nl
    , strstr "renderBackendValue (Extracted.Vfloat _) = \"<float>\"" . nl
    , strstr "renderBackendValue (Extracted.Vsingle _) = \"<float>\"" . nl
    , strstr "renderBackendValue (Extracted.Vptr _ _) = \"<ptr>\"" . nl
    , nl
    , strstr "joinWords :: [Prelude.String] -> Prelude.String" . nl
    , strstr "joinWords [] = \"\"" . nl
    , strstr "joinWords [x] = x" . nl
    , strstr "joinWords (x : xs) = x Prelude.++ Prelude.concatMap (\" \" Prelude.++) xs" . nl
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
    | backendRoot == mecBackendRoot defaultModExtractConfig = toolRoot </> "clightplus" </> "CRIS"
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
