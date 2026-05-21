module Project.A.Pipeline.CoqExtraction where

import System.Directory
import System.Environment
import System.FilePath

import Project.A.Pipeline.Config
import Project.A.Pipeline.ModExtraction
import Project.A.Types
import Project.A.Util.Process

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
            if not (processSucceeded translatorResult)
                then return (failedAfterTranslator translatorLog (TranslatorError (plStderr translatorLog ++ plStdout translatorLog)))
                else do
                    writeFile (caseDir </> "coq" </> "gofile.v") (tprStdout translatorResult)
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
                ghcResult <- runTimedProcess (timeoutGhc timeouts) (Just caseDir) [] "ghc" ghcArgs ""
                let ghcLog = processLog ghcResult
                if not (processSucceeded ghcResult) then
                    return (failedAfterGhc translatorLog coqcLog ghcLog (HaskellCompileError ghcLog))
                else do
                    runResult <- runTimedProcess (timeoutExtractedRun timeouts) (Just caseDir) (riEnv input) ("." </> "coq" </> "extracted" </> "gofile-hs") (riArgs input) (riStdin input)
                    return ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Just (processLog runResult), eoExtraLogs = [], eoResult = Right (obsFromProcess runResult) }
    where
        ghcArgs :: [String]
        ghcArgs = ["-outputdir", "coq" </> "extracted", "-odir", "coq" </> "extracted", "-hidir", "coq" </> "extracted", "coq" </> "extracted" </> "Gofile.hs", "-o", "coq" </> "extracted" </> "gofile-hs"]

runModExtractionAndHaskell :: RunConfig -> FilePath -> RuntimeInput -> ProcessLog -> IO ExtractionOutcome
runModExtractionAndHaskell config caseDir input translatorLog = do
    extractConfig <- modExtractConfigFromEnv (caseDir </> "coq" </> "gofile.v")
    report <- runModExtraction config { cfgWorkDir = caseDir </> "coq" } extractConfig
    let coqcLog = merHarnessLog report
    let extraLogs = modExtractionLogs report
    case merResult report of
        Left err
            | plExitCode coqcLog /= Just 0 -> return (failedAfterCoqcExtra translatorLog coqcLog extraLogs (CoqError coqcLog))
            | otherwise -> return (failedAfterCoqcExtra translatorLog coqcLog extraLogs (ExtractionError err))
        Right hsFile -> runExtractedHaskell config caseDir input translatorLog coqcLog extraLogs hsFile

runExtractedHaskell :: RunConfig -> FilePath -> RuntimeInput -> ProcessLog -> ProcessLog -> [(FilePath, ProcessLog)] -> FilePath -> IO ExtractionOutcome
runExtractedHaskell config caseDir input translatorLog coqcLog extraLogs hsFile = do
    let timeouts = cfgTimeouts config
    ghcResult <- runTimedProcess (timeoutGhc timeouts) (Just caseDir) [] "ghc" (ghcArgs hsFile) ""
    let ghcLog = processLog ghcResult
    if not (processSucceeded ghcResult) then
        return (failedAfterGhcExtra translatorLog coqcLog ghcLog extraLogs (HaskellCompileError ghcLog))
    else do
        runResult <- runTimedProcess (timeoutExtractedRun timeouts) (Just caseDir) (riEnv input) ("." </> "coq" </> "extracted" </> "gofile-hs") (riArgs input) (riStdin input)
        return ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Just (processLog runResult), eoExtraLogs = extraLogs, eoResult = Right (obsFromProcess runResult) }
    where
        ghcArgs hsFile = ["-outputdir", "coq" </> "extracted", "-odir", "coq" </> "extracted", "-hidir", "coq" </> "extracted", hsFile, "-o", "coq" </> "extracted" </> "gofile-hs"]

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
    let opamEnvDir = case opamEnvDirEnv of
            Just dir -> Just dir
            Nothing -> toolRoot
    let coqProjectFiles = case coqProjectFilesEnv of
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
