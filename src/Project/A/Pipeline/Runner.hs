module Project.A.Pipeline.Runner where

import System.Directory
import System.FilePath

import Project.A.Artifact
import Project.A.Fuzz.Corpus
import Project.A.Fuzz.Score
import Project.A.Go.AST
import Project.A.Go.Gen
import Project.A.Pipeline.Config
import Project.A.Pipeline.CoqExtraction
import Project.A.Pipeline.NativeGo
import Project.A.Types

runGeneratedCase :: RunConfig -> CaseId -> Seed -> Size -> IO (CaseReport Program)
runGeneratedCase config caseId seed size = runCase config (genTestCase caseId seed size)

runCase :: RunConfig -> TestCase Program -> IO (CaseReport Program)
runCase config tc = do
    caseDir <- prepareCaseDirectory (cfgWorkDir config) (tcCaseId tc)
    writeInitialArtifacts caseDir tc
    result <- runPreparedPipeline config caseDir (tcInput tc)
    let report = CaseReport { crCaseDir = caseDir, crTestCase = tc, crResult = result, crStatus = classifyResult result }
    writeResult caseDir report
    let score = scoreOfReport report
    writeTextFile (caseDir </> "score.json") (scoreJson score)
    _ <- saveFailureArchive (cfgWorkDir config) report
    corpusDecision <- decideCorpusAdmission (cfgWorkDir config) score report
    writeCorpusDecision caseDir corpusDecision
    commitCorpusAdmission (cfgWorkDir config) corpusDecision report
    return report

runGoFileCase :: RunConfig -> CaseId -> FilePath -> RuntimeInput -> IO (CaseReport FilePath)
runGoFileCase config caseId sourcePath input = do
    absSource <- makeAbsolute sourcePath
    caseDir <- prepareCaseDirectory (cfgWorkDir config) caseId
    copyFile absSource (caseDir </> "gofile.go")
    writeGoFileArtifacts caseDir absSource input
    result <- runPreparedPipeline config caseDir input
    let tc = TestCase { tcCaseId = caseId, tcSeed = 0, tcSize = 0, tcProgram = absSource, tcInput = input }
    let report = CaseReport { crCaseDir = caseDir, crTestCase = tc, crResult = result, crStatus = classifyResult result }
    writeGoFileResult caseDir report
    _ <- saveFailureArchive (cfgWorkDir config) report
    return report

runPreparedPipeline :: RunConfig -> FilePath -> RuntimeInput -> IO PipelineResult
runPreparedPipeline config caseDir input = do
    native <- runNativeGo config caseDir input
    writeProcessLog (caseDir </> "native" </> "gofmt.log") (noGofmtLog native)
    writeProcessLog (caseDir </> "native" </> "build.log") (noBuildLog native)
    maybe (return ()) (writeProcessLog (caseDir </> "native" </> "run.log")) (noRunLog native)
    case noResult native of
        Left buildLog -> return (InvalidGo buildLog)
        Right obsGo -> do
            extraction <- runCoqExtraction config caseDir input
            writeExtractionLogs caseDir extraction
            case eoResult extraction of
                Left failure -> return failure
                Right obsHs -> return (RanBoth obsGo obsHs)

writeExtractionLogs :: FilePath -> ExtractionOutcome -> IO ()
writeExtractionLogs caseDir extraction = do
    maybe (return ()) (writeProcessLog (caseDir </> "coq" </> "translator.log")) (eoTranslatorLog extraction)
    maybe (return ()) (writeProcessLog (caseDir </> "coq" </> "coqc.log")) (eoCoqcLog extraction)
    maybe (return ()) (writeProcessLog (caseDir </> "coq" </> "ghc.log")) (eoGhcLog extraction)
    maybe (return ()) (writeProcessLog (caseDir </> "coq" </> "run.log")) (eoRunLog extraction)
    mapM_ (\(path, logValue) -> writeProcessLog (caseDir </> "coq" </> path) logValue) (eoExtraLogs extraction)
