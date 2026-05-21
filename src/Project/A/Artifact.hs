module Project.A.Artifact where

import System.Directory
import System.FilePath
import Text.Printf

import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Go.Pretty
import Project.A.Types
import qualified Project.A.Util.Json as Json

caseDirectory :: FilePath -> CaseId -> FilePath
caseDirectory workDir caseId = workDir </> "cases" </> printf "%06d" caseId

prepareCaseDirectory :: FilePath -> CaseId -> IO FilePath
prepareCaseDirectory workDir caseId = do
    let dir = caseDirectory workDir caseId
    createDirectoryIfMissing True (dir </> "native")
    createDirectoryIfMissing True (dir </> "coq" </> "extracted")
    return dir

writeInitialArtifacts :: FilePath -> TestCase Program -> IO ()
writeInitialArtifacts dir tc = do
    writeFile (dir </> "seed.json") (seedJson tc)
    writeFile (dir </> "feature.json") (featureJson (featuresOf (tcProgram tc)))
    writeFile (dir </> "gofile.go") (prettyProgram (tcProgram tc))
    writeFile (dir </> "input.stdin") (riStdin (tcInput tc))
    writeFile (dir </> "args.txt") (unlines (riArgs (tcInput tc)))
    writeFile (dir </> "env.json") (envJson (riEnv (tcInput tc)))

writeProcessLog :: FilePath -> ProcessLog -> IO ()
writeProcessLog path logValue = do
    writeFile path (processLogJson logValue)

writeResult :: FilePath -> CaseReport Program -> IO ()
writeResult dir report = writeFile (dir </> "result.json") (caseReportJson report)

seedJson :: TestCase Program -> String
seedJson tc = Json.object [Json.field "caseId" (Json.int (tcCaseId tc)), Json.field "seed" (Json.int (tcSeed tc)), Json.field "size" (Json.int (tcSize tc))]

featureJson :: [Feature] -> String
featureJson features = Json.object [Json.field "features" (Json.list (Json.string . show) features)]

envJson :: [(String, String)] -> String
envJson env = Json.object [Json.field "env" (Json.list pairJson env)] where
    pairJson (key, value) = Json.object [Json.field "key" (Json.string key), Json.field "value" (Json.string value)]

caseReportJson :: CaseReport Program -> String
caseReportJson report = Json.object [Json.field "caseDir" (Json.string (crCaseDir report)), Json.field "status" (Json.string (show (crStatus report))), Json.field "result" (pipelineResultJson (crResult report))]

pipelineResultJson :: PipelineResult -> String
pipelineResultJson (InvalidGo logValue) = tagged "InvalidGo" [Json.field "log" (processLogJson logValue)]
pipelineResultJson (TranslatorError msg) = tagged "TranslatorError" [Json.field "message" (Json.string msg)]
pipelineResultJson (CoqError logValue) = tagged "CoqError" [Json.field "log" (processLogJson logValue)]
pipelineResultJson (ExtractionError msg) = tagged "ExtractionError" [Json.field "message" (Json.string msg)]
pipelineResultJson (HaskellCompileError logValue) = tagged "HaskellCompileError" [Json.field "log" (processLogJson logValue)]
pipelineResultJson (NativeRunError obs) = tagged "NativeRunError" [Json.field "obs" (obsJson obs)]
pipelineResultJson (ExtractedRunError obs) = tagged "ExtractedRunError" [Json.field "obs" (obsJson obs)]
pipelineResultJson (RanBoth obsGo obsHs) = tagged "RanBoth" [Json.field "native" (obsJson obsGo), Json.field "extracted" (obsJson obsHs)]

tagged :: String -> [(String, String)] -> String
tagged tag extra = Json.object (Json.field "tag" (Json.string tag) : extra)

processLogJson :: ProcessLog -> String
processLogJson logValue = Json.object [Json.field "command" (Json.string (plCommand logValue)), Json.field "exitCode" (Json.nullable Json.int (plExitCode logValue)), Json.field "timedOut" (Json.bool (plTimedOut logValue)), Json.field "stdout" (Json.string (plStdout logValue)), Json.field "stderr" (Json.string (plStderr logValue))]

obsJson :: Obs -> String
obsJson obs = Json.object [Json.field "termination" (Json.string (show (obsTermination obs))), Json.field "exitCode" (Json.nullable Json.int (obsExitCode obs)), Json.field "stdout" (Json.string (obsStdout obs)), Json.field "timedOut" (Json.bool (obsTimedOut obs))]
