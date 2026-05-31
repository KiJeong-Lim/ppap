module Project.A.Artifact where

import Data.Char
import Data.List
import System.Directory
import System.FilePath
import Text.Printf

import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Go.Pretty
import Project.A.Types
import qualified Project.A.Util.Json as Json
import Z.System

data StoredSeed
    = StoredSeed
    { storedCaseId :: CaseId
    , storedSeed :: Seed
    , storedSize :: Size
    } deriving (Eq, Ord, Show)

caseDirectory :: FilePath -> CaseId -> FilePath
caseDirectory workDir caseId = workDir </> "cases" </> printf "%06d" caseId

prepareCaseDirectory :: FilePath -> CaseId -> IO FilePath
prepareCaseDirectory workDir caseId = do
    let dir = caseDirectory workDir caseId
    createDirectoryIfMissing True (dir </> "native")
    createDirectoryIfMissing True (dir </> "coq" </> "extracted")
    return dir

copyDirectoryTree :: FilePath -> FilePath -> IO ()
copyDirectoryTree src dst
    = do
        resetPath dst
        createDirectoryIfMissing True dst
        entries <- listDirectory src
        mapM_ copyEntry entries
    where
        copyEntry "go-cache" = return ()
        copyEntry name = do
            let srcPath = src </> name
            let dstPath = dst </> name
            isDir <- doesDirectoryExist srcPath
            if isDir then
                copyDirectoryTree srcPath dstPath
            else
                copyFile srcPath dstPath

resetPath :: FilePath -> IO ()
resetPath path = do
    isDir <- doesDirectoryExist path
    isFile <- doesFileExist path
    if isDir then
        removeDirectoryRecursive path
    else if isFile then
        removeFile path
    else
        return ()

saveFailureArchive :: FilePath -> CaseReport program -> IO (Maybe FilePath)
saveFailureArchive workDir report
    = case crStatus report of
        CaseFail _ -> do
            let dst = workDir </> "failures" </> takeFileName (crCaseDir report)
            copyDirectoryTree (crCaseDir report) dst
            return (Just dst)
        _ -> return Nothing

writeInitialArtifacts :: FilePath -> TestCase Program -> IO ()
writeInitialArtifacts dir tc = do
    writeTextFile (dir </> "seed.json") (seedJson tc)
    writeTextFile (dir </> "feature.json") (featureJson (featuresOf (tcProgram tc)))
    writeTextFile (dir </> "gofile.go") (prettyProgram (tcProgram tc))
    writeRuntimeInputArtifacts dir (tcInput tc)

writeGoFileArtifacts :: FilePath -> FilePath -> RuntimeInput -> IO ()
writeGoFileArtifacts dir sourcePath input = do
    writeTextFile (dir </> "source.json") (sourceJson sourcePath)
    writeRuntimeInputArtifacts dir input

writeRuntimeInputArtifacts :: FilePath -> RuntimeInput -> IO ()
writeRuntimeInputArtifacts dir input = do
    writeTextFile (dir </> "input.stdin") (riStdin input)
    writeTextFile (dir </> "args.txt") (unlines (riArgs input))
    writeTextFile (dir </> "env.json") (envJson (riEnv input))

writeProcessLog :: FilePath -> ProcessLog -> IO ()
writeProcessLog path logValue = writeTextFile path (processLogJson logValue)

writeResult :: FilePath -> CaseReport Program -> IO ()
writeResult dir report = writeTextFile (dir </> "result.json") (caseReportJson report)

writeGoFileResult :: FilePath -> CaseReport FilePath -> IO ()
writeGoFileResult dir report = writeTextFile (dir </> "result.json") (goFileCaseReportJson report)

writeTextFile :: FilePath -> String -> IO ()
writeTextFile path content = do
    _ <- writeFileNow path content
    return ()

readRequiredFile :: FilePath -> IO String
readRequiredFile path = do
    content <- readFileNow path
    case content of
        Just str -> return str
        Nothing -> fail ("cannot read file: " ++ path)

readStoredSeed :: FilePath -> IO (Either String StoredSeed)
readStoredSeed dir = do
    let path = dir </> "seed.json"
    exists <- doesFileExist path
    if not exists then
        return (Left ("seed file does not exist: " ++ path))
    else do
        content <- readRequiredFile path
        return (storedSeedFromJson path content)

storedSeedFromJson :: FilePath -> String -> Either String StoredSeed
storedSeedFromJson path content
    = do
        caseId <- fieldInt "caseId"
        seed <- fieldInt "seed"
        size <- fieldInt "size"
        return StoredSeed { storedCaseId = caseId, storedSeed = seed, storedSize = size }
    where
        fieldInt key
            = case jsonIntField key content of
                Just value -> Right value
                Nothing -> Left ("cannot read integer field " ++ show key ++ " from " ++ path)

jsonIntField :: String -> String -> Maybe Int
jsonIntField key content = findField content where
    prefix = show key ++ ":"
    findField [] = Nothing
    findField str
        | prefix `isPrefixOf` str = readJsonInt (drop (length prefix) str)
        | otherwise = findField (tail str)

readJsonInt :: String -> Maybe Int
readJsonInt str
    = case reads (dropWhile isSpace str) of
        [(value, _)] -> Just value
        _ -> Nothing

seedJson :: TestCase Program -> String
seedJson tc = Json.object [Json.field "caseId" (Json.int (tcCaseId tc)), Json.field "seed" (Json.int (tcSeed tc)), Json.field "size" (Json.int (tcSize tc))]

featureJson :: [Feature] -> String
featureJson features = Json.object [Json.field "features" (Json.list (Json.string . show) features)]

envJson :: [(String, String)] -> String
envJson env = Json.object [Json.field "env" (Json.list pairJson env)] where
    pairJson (key, value) = Json.object [Json.field "key" (Json.string key), Json.field "value" (Json.string value)]

caseReportJson :: CaseReport Program -> String
caseReportJson report = Json.object [Json.field "caseDir" (Json.string (crCaseDir report)), Json.field "status" (Json.string (show (crStatus report))), Json.field "result" (pipelineResultJson (crResult report))]

sourceJson :: FilePath -> String
sourceJson sourcePath = Json.object [Json.field "source" (Json.string sourcePath)]

goFileCaseReportJson :: CaseReport FilePath -> String
goFileCaseReportJson report = Json.object
    [ Json.field "caseDir" (Json.string (crCaseDir report))
    , Json.field "source" (Json.string (tcProgram (crTestCase report)))
    , Json.field "status" (Json.string (show (crStatus report)))
    , Json.field "result" (pipelineResultJson (crResult report))
    ]

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
