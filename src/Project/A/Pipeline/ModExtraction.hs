module Project.A.Pipeline.ModExtraction where

import Data.Char
import Data.List
import Data.Maybe
import System.Directory
import System.FilePath

import Project.A.Pipeline.Config
import Project.A.Types
import Project.A.Util.Process
import Z.System
import Z.Utils

data ModExtractConfig
    = ModExtractConfig
    { mecBackendRoot :: FilePath
    , mecToolRoot :: Maybe FilePath
    , mecCoqcCommand :: FilePath
    , mecOpamEnvDir :: Maybe FilePath
    , mecCoqExtraArgs :: [String]
    , mecCoqProjectFiles :: [FilePath]
    , mecBackendLogical :: String
    , mecBackendLoadDirs :: [FilePath]
    , mecProjectLogical :: String
    , mecCoreRequireModules :: [String]
    , mecExtractionLanguage :: String
    , mecExtractionSupportModule :: String
    , mecExtractionBlacklist :: [String]
    , mecGraTerm :: String
    , mecCoqFile :: Maybe FilePath
    , mecRequireModules :: [String]
    , mecModTerm :: String
    , mecResourceTerm :: String
    , mecArgTerm :: String
    , mecOutputFile :: FilePath
    } deriving (Eq, Ord, Show)

data ModExtractReport
    = ModExtractReport
    { merCaseDir :: FilePath
    , merHarnessFile :: FilePath
    , merExtractedFile :: FilePath
    , merOpamEnvLog :: Maybe ProcessLog
    , merInputLog :: Maybe ProcessLog
    , merHarnessLog :: ProcessLog
    , merResult :: Either String FilePath
    } deriving (Eq, Ord, Show)

defaultModExtractConfig :: ModExtractConfig
defaultModExtractConfig = ModExtractConfig
    { mecBackendRoot = "."
    , mecToolRoot = Nothing
    , mecCoqcCommand = "coqc"
    , mecOpamEnvDir = Nothing
    , mecCoqExtraArgs = []
    , mecCoqProjectFiles = []
    , mecBackendLogical = "__PROJECT_A_BOOT_BACKEND_LOGICAL__"
    , mecBackendLoadDirs = []
    , mecProjectLogical = "ProjectA"
    , mecCoreRequireModules = ["Common", "Any", "Mod", "LMod"]
    , mecExtractionLanguage = "Haskell"
    , mecExtractionSupportModule = "ExtrHaskellBasic"
    , mecExtractionBlacklist = ["List", "String", "Int"]
    , mecGraTerm = "GRAs.nil"
    , mecCoqFile = Nothing
    , mecRequireModules = []
    , mecModTerm = ""
    , mecResourceTerm = "initial"
    , mecArgTerm = "Any.upcast tt"
    , mecOutputFile = "ExtractedMain.hs"
    }

runModExtraction :: RunConfig -> ModExtractConfig -> IO ModExtractReport
runModExtraction config extractConfig = do
    caseDir <- makeAbsolute (cfgWorkDir config </> "mod-extract")
    let coqDir = caseDir </> "coq"
    let extractedDir = coqDir </> "extracted"
    createDirectoryIfMissing True extractedDir
    copiedInput <- copyInputModule coqDir extractConfig
    let harnessFile = coqDir </> "ModHarness.v"
    let outputFile = extractedDir </> mecOutputFile extractConfig
    _ <- writeFileNow harnessFile (modHarnessText copiedInput extractConfig)
    toolEnv <- prepareCoqToolEnv config extractConfig
    case toolEnv of
        Left opamLog -> return ModExtractReport { merCaseDir = caseDir, merHarnessFile = harnessFile, merExtractedFile = outputFile, merOpamEnvLog = Just opamLog, merInputLog = Nothing, merHarnessLog = opamLog, merResult = Left (opamEnvFailure opamLog) }
        Right prepared -> do
            inputLog <- compileInputIfNeeded config extractConfig prepared caseDir copiedInput
            case inputLog of
                Just logValue
                    | not (processLogSucceeded logValue) -> return ModExtractReport { merCaseDir = caseDir, merHarnessFile = harnessFile, merExtractedFile = outputFile, merOpamEnvLog = pctOpamEnvLog prepared, merInputLog = inputLog, merHarnessLog = logValue, merResult = Left (inputCompileFailure logValue) }
                _ -> do
                    harnessArgs <- coqcArgs extractConfig caseDir ["coq" </> "ModHarness.v"]
                    harnessResult <- runTimedProcess (timeoutCoqc (cfgTimeouts config)) (Just caseDir) (pctEnv prepared) (pctCoqcCommand prepared) harnessArgs ""
                    let harnessLog = processLog harnessResult
                    exists <- doesFileExist outputFile
                    let result = if processSucceeded harnessResult && exists then Right outputFile else Left (modExtractionFailure outputFile harnessLog)
                    return ModExtractReport { merCaseDir = caseDir, merHarnessFile = harnessFile, merExtractedFile = outputFile, merOpamEnvLog = pctOpamEnvLog prepared, merInputLog = inputLog, merHarnessLog = harnessLog, merResult = result }

data PreparedCoqTools
    = PreparedCoqTools
    { pctCoqcCommand :: FilePath
    , pctEnv :: [(String, String)]
    , pctOpamEnvLog :: Maybe ProcessLog
    } deriving (Eq, Ord, Show)

prepareCoqToolEnv :: RunConfig -> ModExtractConfig -> IO (Either ProcessLog PreparedCoqTools)
prepareCoqToolEnv config extractConfig
    = case mecOpamEnvDir extractConfig of
        Nothing -> return (Right PreparedCoqTools { pctCoqcCommand = mecCoqcCommand extractConfig, pctEnv = [], pctOpamEnvLog = Nothing })
        Just dir -> do
            result <- runTimedProcess (timeoutCoqc (cfgTimeouts config)) (Just dir) [] "opam" ["env"] ""
            let logValue = processLog result
            if not (processSucceeded result) then
                return (Left logValue)
            else do
                let envOverrides = parseOpamEnv (plStdout logValue)
                coqcCommand <- resolveCoqcCommand (mecCoqcCommand extractConfig) envOverrides
                return (Right PreparedCoqTools { pctCoqcCommand = coqcCommand, pctEnv = envOverrides, pctOpamEnvLog = Just logValue })

resolveCoqcCommand :: FilePath -> [(String, String)] -> IO FilePath
resolveCoqcCommand command envOverrides
    | command /= "coqc" = return command
    | otherwise =
        case lookup "OPAM_SWITCH_PREFIX" envOverrides of
            Nothing -> return command
            Just prefix -> do
                let opamCoqc = prefix </> "bin" </> "coqc"
                exists <- doesFileExist opamCoqc
                return (if exists then opamCoqc else command)

parseOpamEnv :: String -> [(String, String)]
parseOpamEnv = mapMaybe parseOpamEnvLine . lines

parseOpamEnvLine :: String -> Maybe (String, String)
parseOpamEnvLine line
    = case break (== '=') line of
        (key, '=' : rest)
            | not (null key) && all isEnvKeyChar key -> Just (key, parseOpamValue rest)
        _ -> Nothing

isEnvKeyChar :: Char -> Bool
isEnvKeyChar ch = isAlphaNum ch || ch == '_'

parseOpamValue :: String -> String
parseOpamValue ('\'' : rest) = takeWhile (/= '\'') rest
parseOpamValue rest = takeWhile (\ch -> ch /= ';' && not (isSpace ch)) rest

copyInputModule :: FilePath -> ModExtractConfig -> IO (Maybe String)
copyInputModule coqDir extractConfig
    = case mecCoqFile extractConfig of
        Nothing -> return Nothing
        Just path -> do
            content <- maybe (fail ("cannot read file: " ++ path)) return =<< readFileNow path
            _ <- writeFileNow (coqDir </> "Input.v") content
            return (Just (mecProjectLogical extractConfig ++ ".Input"))

compileInputIfNeeded :: RunConfig -> ModExtractConfig -> PreparedCoqTools -> FilePath -> Maybe String -> IO (Maybe ProcessLog)
compileInputIfNeeded _ _ _ _ Nothing = return Nothing
compileInputIfNeeded config extractConfig prepared caseDir (Just _) = do
    args <- coqcArgs extractConfig caseDir ["coq" </> "Input.v"]
    result <- runTimedProcess (timeoutCoqc (cfgTimeouts config)) (Just caseDir) (pctEnv prepared) (pctCoqcCommand prepared) args ""
    return (Just (processLog result))

coqcArgs :: ModExtractConfig -> FilePath -> [String] -> IO [String]
coqcArgs extractConfig caseDir sourceFiles = do
    loadPathArgs <- coqProjectLoadPath extractConfig
    return (mecCoqExtraArgs extractConfig ++ loadPathArgs ++ ["-R", caseDir </> "coq", mecProjectLogical extractConfig] ++ sourceFiles)

coqProjectLoadPath :: ModExtractConfig -> IO [String]
coqProjectLoadPath extractConfig
    | not (null (mecCoqProjectFiles extractConfig)) = concat <$> mapM coqProjectArgsFromFile (mecCoqProjectFiles extractConfig)
    | otherwise = return (concat [["-R", mecBackendRoot extractConfig </> dir, mecBackendLogical extractConfig] | dir <- mecBackendLoadDirs extractConfig])

coqProjectArgsFromFile :: FilePath -> IO [String]
coqProjectArgsFromFile path = do
    absPath <- makeAbsolute path
    content <- maybe (fail ("cannot read file: " ++ absPath)) return =<< readFileNow absPath
    return (coqProjectArgs (takeDirectory absPath) content)

coqProjectArgs :: FilePath -> String -> [String]
coqProjectArgs baseDir content = go (words (unlines (map stripCoqProjectComment (lines content)))) where
    go [] = []
    go ("-R" : dir : logical : rest) = "-R" : coqProjectPath baseDir dir : logical : go rest
    go ("-Q" : dir : logical : rest) = "-Q" : coqProjectPath baseDir dir : logical : go rest
    go ("-I" : dir : rest) = "-I" : coqProjectPath baseDir dir : go rest
    go ("-include" : dir : rest) = "-include" : coqProjectPath baseDir dir : go rest
    go ("-arg" : arg : rest) = arg : go rest
    go ("-docroot" : _ : rest) = go rest
    go (_ : rest) = go rest

stripCoqProjectComment :: String -> String
stripCoqProjectComment = takeWhile (/= '#')

coqProjectPath :: FilePath -> FilePath -> FilePath
coqProjectPath baseDir path
    | isAbsolute path = normalise path
    | otherwise = normalise (baseDir </> path)

modHarnessText :: Maybe String -> ModExtractConfig -> String
modHarnessText copiedInput extractConfig = modHarnessText' copiedInput extractConfig ""

modHarnessText' :: Maybe String -> ModExtractConfig -> ShowS
modHarnessText' copiedInput extractConfig
    = strcat
        [ strstr "Require Coq.extraction.Extraction." . nl
        , if null (mecExtractionSupportModule extractConfig) then id else strstr "Require Import " . strstr (mecExtractionSupportModule extractConfig) . strstr "." . nl
        , if null (mecExtractionLanguage extractConfig) then id else strstr "Extraction Language " . strstr (mecExtractionLanguage extractConfig) . strstr "." . nl
        , nl
        , strcat [ strstr "Require Import " . strstr moduleName . strstr "." . nl | moduleName <- coreModules ]
        , if mecExtractionLanguage extractConfig == "Haskell" then strstr "From go2c Require Import golang_prelude." . nl else id
        , strcat [ strstr "Require Import " . strstr moduleName . strstr "." . nl | moduleName <- importModules ]
        , nl
        , if null (mecExtractionBlacklist extractConfig) then id else strstr "Extraction Blacklist " . strstr (unwords (mecExtractionBlacklist extractConfig)) . strstr "." . nl
        , if mecExtractionLanguage extractConfig == "Haskell" then strstr "Extract Constant excluded_middle_informative => \"Prelude.True\"." . nl else id
        , if mecExtractionLanguage extractConfig == "Haskell" then go2cHaskellExtractionAliases else id
        , nl
        , strstr "Definition project_a_gra : GRA := " . strstr (mecGraTerm extractConfig) . strstr "." . nl
        , strstr "Definition project_a_target_mod : @Mod.t project_a_gra := " . strstr (mecModTerm extractConfig) . strstr "." . nl
        , strstr "Definition project_a_target_lmod : LMod.t := @Mod.to_lmod project_a_gra project_a_target_mod (" . strstr (mecResourceTerm extractConfig) . strstr ")." . nl
        , strstr "Definition project_a_target_itr := LMod.compile project_a_target_lmod (" . strstr (mecArgTerm extractConfig) . strstr ")." . nl
        , nl
        , strstr "Extraction " . shows ("coq" </> "extracted" </> mecOutputFile extractConfig) . strstr " project_a_target_itr." . nl
        ]
    where
        coreModules = mecCoreRequireModules extractConfig
        importModules = nub (maybe [] (: []) copiedInput ++ mecRequireModules extractConfig)

go2cHaskellExtractionAliases :: ShowS
go2cHaskellExtractionAliases = strcat
    [ strstr "Extract Inductive C.val => \"Val\"" . nl
    , strstr "  [ \"Vundef\" \"Vint\" \"Vlong\" \"Vfloat\" \"Vsingle\" \"Vptr\" ]." . nl
    , strstr "Extract Inductive C.AST.memory_chunk => \"Memory_chunk\"" . nl
    , strstr "  [ \"Mint8signed\" \"Mint8unsigned\" \"Mint16signed\" \"Mint16unsigned\"" . nl
    , strstr "    \"Mint32\" \"Mint64\" \"Mfloat32\" \"Mfloat64\" \"Many32\" \"Many64\" ]." . nl
    ]

modExtractionFailure :: FilePath -> ProcessLog -> String
modExtractionFailure outputFile logValue = concat
    [ "coqc failed or expected extracted file does not exist: "
    , outputFile
    , "; exit="
    , show (plExitCode logValue)
    , "; timedOut="
    , show (plTimedOut logValue)
    ]

opamEnvFailure :: ProcessLog -> String
opamEnvFailure logValue = concat
    [ "opam env failed: exit="
    , show (plExitCode logValue)
    , "; timedOut="
    , show (plTimedOut logValue)
    ]

inputCompileFailure :: ProcessLog -> String
inputCompileFailure logValue = concat
    [ "input Coq file failed to compile: exit="
    , show (plExitCode logValue)
    , "; timedOut="
    , show (plTimedOut logValue)
    ]

processLogSucceeded :: ProcessLog -> Bool
processLogSucceeded logValue = plExitCode logValue == Just 0
