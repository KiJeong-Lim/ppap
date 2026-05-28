module Project.A.Pipeline.TestItrExtraction where

import Data.List
import System.Directory
import System.FilePath

import Project.A.Pipeline.Config
import Project.A.Pipeline.ModExtraction
import Project.A.Types
import Project.A.Util.Process
import Z.System
import Z.Utils

data TestItrExtractConfig
    = TestItrExtractConfig
    { tieModConfig :: ModExtractConfig
    , tieTerm :: String
    , tieGhcCommand :: FilePath
    , tieBinaryFile :: FilePath
    } deriving (Eq, Ord, Show)

data TestItrExtractReport
    = TestItrExtractReport
    { tierCaseDir :: FilePath
    , tierHarnessFile :: FilePath
    , tierExtractedFile :: FilePath
    , tierDriverFile :: FilePath
    , tierBinaryFile :: FilePath
    , tierOpamEnvLog :: Maybe ProcessLog
    , tierInputLog :: Maybe ProcessLog
    , tierHarnessLog :: Maybe ProcessLog
    , tierGhcLog :: Maybe ProcessLog
    , tierResult :: Either String FilePath
    } deriving (Eq, Ord, Show)

defaultTestItrExtractConfig :: TestItrExtractConfig
defaultTestItrExtractConfig = TestItrExtractConfig
    { tieModConfig = defaultModExtractConfig { mecModTerm = "", mecOutputFile = "ExtractedMain.hs" }
    , tieTerm = "test_itr"
    , tieGhcCommand = "ghc"
    , tieBinaryFile = "test-itr-hs"
    }

runTestItrExtraction :: RunConfig -> TestItrExtractConfig -> IO TestItrExtractReport
runTestItrExtraction config testConfig = do
    let extractConfig = tieModConfig testConfig
    caseDir <- makeAbsolute (cfgWorkDir config </> "test-itr-extract")
    let coqDir = caseDir </> "coq"
    let extractedDir = coqDir </> "extracted"
    createDirectoryIfMissing True extractedDir
    copiedInput <- copyInputModule coqDir extractConfig
    let harnessFile = coqDir </> "TestItrHarness.v"
    let outputFile = extractedDir </> mecOutputFile extractConfig
    let driverFile = extractedDir </> "Main.hs"
    let binaryFile = extractedDir </> tieBinaryFile testConfig
    _ <- writeFileNow harnessFile (testItrHarnessText copiedInput testConfig)
    toolEnv <- prepareCoqToolEnv config extractConfig
    case toolEnv of
        Left opamLog -> return (failedReport caseDir harnessFile outputFile driverFile binaryFile (Just opamLog) Nothing Nothing Nothing (opamEnvFailure opamLog))
        Right prepared -> do
            inputLog <- compileInputIfNeeded config extractConfig prepared caseDir copiedInput
            case inputLog of
                Just logValue
                    | not (processLogSucceeded logValue) ->
                        return (failedReport caseDir harnessFile outputFile driverFile binaryFile (pctOpamEnvLog prepared) inputLog Nothing Nothing (inputCompileFailure logValue))
                _ -> do
                    harnessArgs <- coqcArgs extractConfig caseDir ["coq" </> "TestItrHarness.v"]
                    harnessResult <- runTimedProcess (timeoutCoqc (cfgTimeouts config)) (Just caseDir) (pctEnv prepared) (pctCoqcCommand prepared) harnessArgs ""
                    let harnessLog = processLog harnessResult
                    exists <- doesFileExist outputFile
                    if not (processSucceeded harnessResult) || not exists then
                        return (failedReport caseDir harnessFile outputFile driverFile binaryFile (pctOpamEnvLog prepared) inputLog (Just harnessLog) Nothing (testItrExtractionFailure outputFile harnessLog))
                    else do
                        _ <- writeFileNow driverFile (testItrDriverText (takeBaseName outputFile))
                        ghcResult <- runTimedProcess (timeoutGhc (cfgTimeouts config)) (Just caseDir) [] (tieGhcCommand testConfig) (ghcArgs extractedDir driverFile binaryFile) ""
                        let ghcLog = processLog ghcResult
                        if not (processSucceeded ghcResult) then
                            return (failedReport caseDir harnessFile outputFile driverFile binaryFile (pctOpamEnvLog prepared) inputLog (Just harnessLog) (Just ghcLog) (testItrGhcFailure ghcLog))
                        else
                            return TestItrExtractReport { tierCaseDir = caseDir, tierHarnessFile = harnessFile, tierExtractedFile = outputFile, tierDriverFile = driverFile, tierBinaryFile = binaryFile, tierOpamEnvLog = pctOpamEnvLog prepared, tierInputLog = inputLog, tierHarnessLog = Just harnessLog, tierGhcLog = Just ghcLog, tierResult = Right binaryFile}

failedReport :: FilePath -> FilePath -> FilePath -> FilePath -> FilePath -> Maybe ProcessLog -> Maybe ProcessLog -> Maybe ProcessLog -> Maybe ProcessLog -> String -> TestItrExtractReport
failedReport caseDir harnessFile outputFile driverFile binaryFile opamLog inputLog harnessLog ghcLog err = TestItrExtractReport
    { tierCaseDir = caseDir
    , tierHarnessFile = harnessFile
    , tierExtractedFile = outputFile
    , tierDriverFile = driverFile
    , tierBinaryFile = binaryFile
    , tierOpamEnvLog = opamLog
    , tierInputLog = inputLog
    , tierHarnessLog = harnessLog
    , tierGhcLog = ghcLog
    , tierResult = Left err
    }

testItrHarnessText :: Maybe String -> TestItrExtractConfig -> String
testItrHarnessText copiedInput testConfig = testItrHarnessText' copiedInput testConfig ""

testItrHarnessText' :: Maybe String -> TestItrExtractConfig -> ShowS
testItrHarnessText' copiedInput testConfig
    = strcat
        [ strstr "Require Coq.extraction.Extraction." . nl
        , strstr "Require Import Coq.Logic.ClassicalDescription." . nl
        , if null (mecExtractionSupportModule extractConfig) then id else strstr "Require Import " . strstr (mecExtractionSupportModule extractConfig) . strstr "." . nl
        , if null (mecExtractionLanguage extractConfig) then id else strstr "Extraction Language " . strstr (mecExtractionLanguage extractConfig) . strstr "." . nl
        , nl
        , strcat [ strstr "Require Import " . strstr moduleName . strstr "." . nl | moduleName <- importModules ]
        , nl
        , if null (mecExtractionBlacklist extractConfig) then id else strstr "Extraction Blacklist " . strstr (unwords (mecExtractionBlacklist extractConfig)) . strstr "." . nl
        , if mecExtractionLanguage extractConfig == "Haskell" then strstr "Extract Constant excluded_middle_informative => \"Prelude.True\"." . nl else id
        , nl
        , strstr "Definition project_a_test_itr := " . strstr (tieTerm testConfig) . strstr "." . nl
        , nl
        , strstr "Extraction " . shows ("coq" </> "extracted" </> mecOutputFile extractConfig) . strstr " project_a_test_itr." . nl
        ]
    where
        extractConfig = tieModConfig testConfig
        importModules = nub (maybe [] (: []) copiedInput ++ mecRequireModules extractConfig)

testItrDriverText :: String -> String
testItrDriverText extractedModule = testItrDriverText' extractedModule ""

testItrDriverText' :: String -> ShowS
testItrDriverText' extractedModule = strcat
    [ strstr "module Main where" . nl
    , nl
    , strstr "import qualified Prelude" . nl
    , strstr "import qualified " . strstr extractedModule . strstr " as Extracted" . nl
    , nl
    , strstr "main :: Prelude.IO ()" . nl
    , strstr "main = Extracted.project_a_test_itr `Prelude.seq` Prelude.putStrLn \"project_a_test_itr linked\"" . nl
    ]

ghcArgs :: FilePath -> FilePath -> FilePath -> [String]
ghcArgs extractedDir driverFile binaryFile =
    [ "-XNoPolyKinds"
    , "-i" ++ extractedDir
    , "-outputdir", extractedDir
    , "-odir", extractedDir
    , "-hidir", extractedDir
    , driverFile
    , "-o", binaryFile
    ]

testItrExtractionFailure :: FilePath -> ProcessLog -> String
testItrExtractionFailure outputFile logValue = concat
    [ "coqc failed or expected extracted test_itr file does not exist: "
    , outputFile
    , "; exit="
    , show (plExitCode logValue)
    , "; timedOut="
    , show (plTimedOut logValue)
    ]

testItrGhcFailure :: ProcessLog -> String
testItrGhcFailure logValue = concat
    [ "ghc failed while compiling extracted test_itr: exit="
    , show (plExitCode logValue)
    , "; timedOut="
    , show (plTimedOut logValue)
    ]
