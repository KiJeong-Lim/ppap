module Project.A.Pipeline.CoqExtraction where

import System.Directory
import System.Environment
import System.FilePath

import Project.A.Pipeline.Config
import Project.A.Types
import Project.A.Util.Process

data ExtractionOutcome
    = ExtractionOutcome
    { eoTranslatorLog :: Maybe ProcessLog
    , eoCoqcLog :: Maybe ProcessLog
    , eoGhcLog :: Maybe ProcessLog
    , eoRunLog :: Maybe ProcessLog
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
                    runCoqcAndHaskell config caseDir input translatorLog

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
                    return ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Just (processLog runResult), eoResult = Right (obsFromProcess runResult) }
    where
        ghcArgs :: [String]
        ghcArgs = ["-outputdir", "coq" </> "extracted", "-odir", "coq" </> "extracted", "-hidir", "coq" </> "extracted", "coq" </> "extracted" </> "Gofile.hs", "-o", "coq" </> "extracted" </> "gofile-hs"]

failedExtraction :: PipelineResult -> ExtractionOutcome
failedExtraction result = ExtractionOutcome { eoTranslatorLog = Nothing, eoCoqcLog = Nothing, eoGhcLog = Nothing, eoRunLog = Nothing, eoResult = Left result }

failedAfterTranslator :: ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterTranslator translatorLog result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Nothing, eoGhcLog = Nothing, eoRunLog = Nothing, eoResult = Left result }

failedAfterCoqc :: ProcessLog -> ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterCoqc translatorLog coqcLog result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Nothing, eoRunLog = Nothing, eoResult = Left result }

failedAfterGhc :: ProcessLog -> ProcessLog -> ProcessLog -> PipelineResult -> ExtractionOutcome
failedAfterGhc translatorLog coqcLog ghcLog result = ExtractionOutcome { eoTranslatorLog = Just translatorLog, eoCoqcLog = Just coqcLog, eoGhcLog = Just ghcLog, eoRunLog = Nothing, eoResult = Left result }
