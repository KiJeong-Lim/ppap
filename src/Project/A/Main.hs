module Project.A.Main
    ( main
    , mainWithArgs
    ) where

import Control.Monad
import Data.List
import System.Directory
import System.Environment
import System.FilePath

import Project.A.Artifact
import Project.A.Fuzz.Summary
import Project.A.Fuzz.Shrink
import Project.A.Fuzz.Score
import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Go.Gen
import Project.A.Go.Mutate
import Project.A.Go.Pretty
import Project.A.Go.Shrink
import Project.A.Pipeline.Config
import Project.A.Pipeline.ModExtraction
import Project.A.Pipeline.Runner
import Project.A.Types
import Z.Utils

main :: IO ()
main = getArgs >>= mainWithArgs

mainWithArgs :: [String] -> IO ()
mainWithArgs args
    = case parseCommand args of
        Help -> putStr helpText
        One options -> runOne options
        Fuzz options -> runFuzz options
        PrintGo options -> runPrintGo options
        Search options -> runSearch options
        Replay options -> runReplay options
        Shrink options -> runShrink options
        ModExtract options -> runModExtract options

data Command
    = Help
    | One Options
    | Fuzz Options
    | PrintGo Options
    | Search Options
    | Replay Options
    | Shrink Options
    | ModExtract ModExtractOptions
    deriving (Eq, Ord, Show)

data ModExtractOptions
    = ModExtractOptions
    { modOptWorkDir :: FilePath
    , modOptBackendRoot :: FilePath
    , modOptToolRoot :: Maybe FilePath
    , modOptCoqcCommand :: FilePath
    , modOptOpamEnvDir :: Maybe FilePath
    , modOptCoqExtraArgs :: [String]
    , modOptCoqProjectFiles :: [FilePath]
    , modOptBackendLogical :: String
    , modOptBackendLoadDirs :: [FilePath]
    , modOptProjectLogical :: String
    , modOptCoreRequires :: [String]
    , modOptExtractionLanguage :: String
    , modOptExtractionSupport :: String
    , modOptExtractionBlacklist :: [String]
    , modOptGraTerm :: String
    , modOptCoqFile :: Maybe FilePath
    , modOptRequires :: [String]
    , modOptModTerm :: String
    , modOptResourceTerm :: String
    , modOptArgTerm :: String
    , modOptOutputFile :: FilePath
    } deriving (Eq, Ord, Show)

defaultModExtractOptions :: ModExtractOptions
defaultModExtractOptions = ModExtractOptions
    { modOptWorkDir = cfgWorkDir defaultRunConfig
    , modOptBackendRoot = mecBackendRoot defaultModExtractConfig
    , modOptToolRoot = mecToolRoot defaultModExtractConfig
    , modOptCoqcCommand = mecCoqcCommand defaultModExtractConfig
    , modOptOpamEnvDir = mecOpamEnvDir defaultModExtractConfig
    , modOptCoqExtraArgs = mecCoqExtraArgs defaultModExtractConfig
    , modOptCoqProjectFiles = mecCoqProjectFiles defaultModExtractConfig
    , modOptBackendLogical = mecBackendLogical defaultModExtractConfig
    , modOptBackendLoadDirs = mecBackendLoadDirs defaultModExtractConfig
    , modOptProjectLogical = mecProjectLogical defaultModExtractConfig
    , modOptCoreRequires = mecCoreRequireModules defaultModExtractConfig
    , modOptExtractionLanguage = mecExtractionLanguage defaultModExtractConfig
    , modOptExtractionSupport = mecExtractionSupportModule defaultModExtractConfig
    , modOptExtractionBlacklist = mecExtractionBlacklist defaultModExtractConfig
    , modOptGraTerm = mecGraTerm defaultModExtractConfig
    , modOptCoqFile = Nothing
    , modOptRequires = []
    , modOptModTerm = ""
    , modOptResourceTerm = mecResourceTerm defaultModExtractConfig
    , modOptArgTerm = mecArgTerm defaultModExtractConfig
    , modOptOutputFile = mecOutputFile defaultModExtractConfig
    }

data Options
    = Options
    { optSeed :: Seed
    , optSize :: Size
    , optCases :: Int
    , optWorkDir :: FilePath
    , optExplicitWorkDir :: Maybe FilePath
    , optCaseDir :: Maybe FilePath
    } deriving (Eq, Ord, Show)

defaultOptions :: Options
defaultOptions = Options { optSeed = 1, optSize = 3, optCases = 1, optWorkDir = cfgWorkDir defaultRunConfig, optExplicitWorkDir = Nothing, optCaseDir = Nothing }

parseCommand :: [String] -> Command
parseCommand rawArgs
    = case map normalizeArg rawArgs of
        [] -> Help
        "help" : _ -> Help
        "one" : rest -> One (parseOptions rest)
        "fuzz" : rest -> Fuzz (parseOptions rest)
        "print-go" : rest -> PrintGo (parseOptions rest)
        "search" : rest -> Search (parseOptions rest)
        "replay" : rest -> Replay (parseOptions rest)
        "shrink" : rest -> Shrink (parseOptions rest)
        "mod-extract" : rest -> ModExtract (parseModExtractOptions rest)
        "--help" : _ -> Help
        unknown : _ -> if unknown == "one" || unknown == "--one" then One defaultOptions else Help

parseOptions :: [String] -> Options
parseOptions args = defaultOptions { optSeed = intOption "seed" (optSeed defaultOptions) args, optSize = intOption "size" (optSize defaultOptions) args, optCases = max 1 (intOption "cases" (optCases defaultOptions) args), optWorkDir = stringOption "workdir" (optWorkDir defaultOptions) args, optExplicitWorkDir = stringOptionMaybe "workdir" args, optCaseDir = stringOptionMaybe "case-dir" args }

parseModExtractOptions :: [String] -> ModExtractOptions
parseModExtractOptions args = defaultModExtractOptions
    { modOptWorkDir = stringOption "workdir" (modOptWorkDir defaultModExtractOptions) args
    , modOptBackendRoot = stringOption "backend-root" (modOptBackendRoot defaultModExtractOptions) args
    , modOptToolRoot = stringOptionMaybe "tool-root" args
    , modOptCoqcCommand = stringOption "coqc" (modOptCoqcCommand defaultModExtractOptions) args
    , modOptOpamEnvDir = stringOptionMaybe "opam-env-dir" args
    , modOptCoqExtraArgs = commaWords (stringOption "coq-args" "" args)
    , modOptCoqProjectFiles = commaWords (stringOption "coqproject" "" args)
    , modOptBackendLogical = stringOption "backend-logical" (modOptBackendLogical defaultModExtractOptions) args
    , modOptBackendLoadDirs = commaWordsDefault (modOptBackendLoadDirs defaultModExtractOptions) (stringOption "backend-dirs" "" args)
    , modOptProjectLogical = stringOption "project-logical" (modOptProjectLogical defaultModExtractOptions) args
    , modOptCoreRequires = commaWordsDefault (modOptCoreRequires defaultModExtractOptions) (stringOption "core-require" "" args)
    , modOptExtractionLanguage = stringOption "extraction-language" (modOptExtractionLanguage defaultModExtractOptions) args
    , modOptExtractionSupport = stringOption "extraction-support" (modOptExtractionSupport defaultModExtractOptions) args
    , modOptExtractionBlacklist = commaWordsDefault (modOptExtractionBlacklist defaultModExtractOptions) (stringOption "blacklist" "" args)
    , modOptGraTerm = stringOption "gra" (modOptGraTerm defaultModExtractOptions) args
    , modOptCoqFile = stringOptionMaybe "coq-file" args
    , modOptRequires = commaWords (stringOption "require" "" args)
    , modOptModTerm = stringOption "mod" (modOptModTerm defaultModExtractOptions) args
    , modOptResourceTerm = stringOption "resource" (modOptResourceTerm defaultModExtractOptions) args
    , modOptArgTerm = stringOption "arg" (modOptArgTerm defaultModExtractOptions) args
    , modOptOutputFile = stringOption "output" (modOptOutputFile defaultModExtractOptions) args
    }

normalizeArg :: String -> String
normalizeArg arg
    = case stripPrefix "--" arg of
        Just rest -> rest
        Nothing -> arg

intOption :: String -> Int -> [String] -> Int
intOption key fallback args
    = case stringOptionMaybe key args >>= readMaybeInt of
        Just n -> n
        Nothing -> fallback

stringOption :: String -> String -> [String] -> String
stringOption key fallback args = maybe fallback id (stringOptionMaybe key args)

stringOptionMaybe :: String -> [String] -> Maybe String
stringOptionMaybe key rawArgs = go (map normalizeArg rawArgs) where
    prefix = key ++ "="

    go [] = Nothing
    go [arg]
        | prefix `isPrefixOf` arg = Just (drop (length prefix) arg)
        | otherwise = Nothing
    go (arg : value : rest)
        | arg == key = Just value
        | prefix `isPrefixOf` arg = Just (drop (length prefix) arg)
        | otherwise = go (value : rest)

commaWords :: String -> [String]
commaWords "" = []
commaWords str = filter (not . null) (map trim (splitComma str))

commaWordsDefault :: [String] -> String -> [String]
commaWordsDefault fallback "" = fallback
commaWordsDefault _ str = commaWords str

splitComma :: String -> [String]
splitComma str
    = case break (== ',') str of
        (word, "") -> [word]
        (word, _ : rest) -> word : splitComma rest

trim :: String -> String
trim = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

readMaybeInt :: String -> Maybe Int
readMaybeInt str
    = case reads str of
        [(n, "")] -> Just n
        _ -> Nothing

runOne :: Options -> IO ()
runOne options = do
    report <- runGeneratedCase (configFromOptions options) 1 (optSeed options) (optSize options)
    putStrLn ("case-dir: " ++ crCaseDir report)
    putStrLn ("status: " ++ show (crStatus report))
    putStrLn ("score: " ++ scoreSummary (scoreOfReport report))
    putStrLn ("result: " ++ show (crResult report))

runFuzz :: Options -> IO ()
runFuzz options
    = do
        summary <- foldM runStep emptySummary [1 .. optCases options]
        putStr (renderSummary summary)
    where
        config = configFromOptions options

        runStep summary caseId = do
            let seed = optSeed options + caseId - 1
            report <- runGeneratedCase config caseId seed (optSize options)
            putStrLn (show caseId ++ ": " ++ show (crStatus report) ++ " " ++ scoreSummary (scoreOfReport report) ++ " " ++ crCaseDir report)
            return (addReport summary report)

runPrintGo :: Options -> IO ()
runPrintGo options = mapM_ printCase [1 .. optCases options] where
    printCase caseId = do
        let seed = optSeed options + caseId - 1
        putStrLn ("// randomgen case " ++ show caseId ++ ", seed=" ++ show seed ++ ", size=" ++ show (optSize options))
        putStr (prettyProgram (genProgram seed (optSize options)))
        when (caseId < optCases options) (putStrLn "")

runSearch :: Options -> IO ()
runSearch options
    = do
        (summary, _) <- foldM runStep (emptySummary, Nothing) [1 .. optCases options]
        putStr (renderSummary summary)
    where
        config = configFromOptions options

        runStep (summary, best) caseId = do
            let seed = optSeed options + caseId - 1
            let program = case best of
                    Nothing -> genProgram seed (optSize options)
                    Just (bestProgram, _) -> mutateProgram seed bestProgram
            let tc0 = genTestCase caseId seed (optSize options)
            let tc = tc0 { tcProgram = program, tcSize = programNodeCount program }
            report <- runCase config tc
            let score = scoreOfReport report
            putStrLn (show caseId ++ ": " ++ show (crStatus report) ++ " " ++ scoreSummary score ++ " " ++ crCaseDir report)
            return (addReport summary report, updateSearchBest program score best)

updateSearchBest :: Program -> Score -> Maybe (Program, Int) -> Maybe (Program, Int)
updateSearchBest program score current
    = case score of
        Interesting n _ -> case current of
            Nothing -> Just (program, n)
            Just (_, best)
                | n < best -> Just (program, n)
                | otherwise -> current
        _ -> current

runReplay :: Options -> IO ()
runReplay options
    = withStoredSeed "replay" options $ \caseDir stored -> do
        let config = defaultRunConfig { cfgWorkDir = replayWorkDir options caseDir }
        report <- runGeneratedCase config (storedCaseId stored) (storedSeed stored) (storedSize stored)
        putStrLn ("case-dir: " ++ crCaseDir report)
        putStrLn ("status: " ++ show (crStatus report))
        putStrLn ("result: " ++ show (crResult report))

runShrink :: Options -> IO ()
runShrink options
    = withStoredSeed "shrink" options $ \caseDir -> \stored -> do
        let workDir = shrinkWorkDir options caseDir
        resetDirectory workDir
        let config = defaultRunConfig { cfgWorkDir = workDir }
        let tc = TestCase { tcCaseId = storedCaseId stored, tcSeed = storedSeed stored, tcSize = storedSize stored, tcProgram = genProgram (storedSeed stored) (storedSize stored), tcInput = RuntimeInput { riArgs = [], riStdin = "", riEnv = [] } }
        result <- runShrinkSearch config tc
        let shrunkDir = caseDir </> "shrunk"
        writeShrunkArtifacts shrunkDir result
        regressionDir <- saveRegressionArchive caseDir shrunkDir result
        putStrLn ("original-status: " ++ show (crStatus (srOriginalReport result)))
        putStrLn ("shrunk-status: " ++ show (crStatus (srFinalReport result)))
        putStrLn ("tested: " ++ show (srTested result))
        putStrLn ("accepted: " ++ show (srAccepted result))
        putStrLn ("shrunk-dir: " ++ shrunkDir)
        maybe (return ()) (\dir -> putStrLn ("regression-dir: " ++ dir)) regressionDir

saveRegressionArchive :: FilePath -> FilePath -> ShrinkResult -> IO (Maybe FilePath)
saveRegressionArchive caseDir shrunkDir result
    = case crStatus (srFinalReport result) of
        CaseFail _ -> do
            let dst = takeDirectory (takeDirectory caseDir) </> "regressions" </> takeFileName caseDir
            copyDirectoryTree shrunkDir dst
            return (Just dst)
        _ -> return Nothing

runModExtract :: ModExtractOptions -> IO ()
runModExtract rawOptions = do
    options <- applyModExtractEnv rawOptions
    if null (modOptModTerm options) then
        putStrLn "mod-extract-error: --mod=TERM is required"
    else do
        let workDir = modOptWorkDir options
        resetDirectory (workDir </> "mod-extract")
        report <- runModExtraction defaultRunConfig { cfgWorkDir = workDir } (modConfigFromOptions options)
        maybe (return ()) (writeProcessLog (merCaseDir report </> "coq" </> "opam-env.log")) (merOpamEnvLog report)
        maybe (return ()) (writeProcessLog (merCaseDir report </> "coq" </> "input.log")) (merInputLog report)
        writeProcessLog (merCaseDir report </> "coq" </> "harness.log") (merHarnessLog report)
        putStrLn ("case-dir: " ++ merCaseDir report)
        putStrLn ("harness: " ++ merHarnessFile report)
        case merResult report of
            Right path -> putStrLn ("extracted: " ++ path)
            Left err -> putStrLn ("mod-extract-error: " ++ err)

applyModExtractEnv :: ModExtractOptions -> IO ModExtractOptions
applyModExtractEnv options = do
    workDir <- envString "PROJECT_A_WORKDIR" (modOptWorkDir defaultModExtractOptions) (modOptWorkDir options)
    toolRoot <- envMaybe "PROJECT_A_TOOL_ROOT" (modOptToolRoot options)
    backendRoot <- envString "PROJECT_A_BACKEND_ROOT" (modOptBackendRoot defaultModExtractOptions) (modOptBackendRoot options)
    coqcCommand <- envString "PROJECT_A_COQC" (modOptCoqcCommand defaultModExtractOptions) (modOptCoqcCommand options)
    opamEnvDir <- envMaybe "PROJECT_A_OPAM_ENV_DIR" (modOptOpamEnvDir options)
    coqExtraArgs <- envList "PROJECT_A_COQ_ARGS" (modOptCoqExtraArgs defaultModExtractOptions) (modOptCoqExtraArgs options)
    coqProjectFiles <- envList "PROJECT_A_COQPROJECTS" (modOptCoqProjectFiles defaultModExtractOptions) (modOptCoqProjectFiles options)
    backendLogical <- envString "PROJECT_A_BACKEND_LOGICAL" (modOptBackendLogical defaultModExtractOptions) (modOptBackendLogical options)
    backendLoadDirs <- envList "PROJECT_A_BACKEND_DIRS" (modOptBackendLoadDirs defaultModExtractOptions) (modOptBackendLoadDirs options)
    projectLogical <- envString "PROJECT_A_PROJECT_LOGICAL" (modOptProjectLogical defaultModExtractOptions) (modOptProjectLogical options)
    coreRequires <- envList "PROJECT_A_BACKEND_CORE_REQUIRE" (modOptCoreRequires defaultModExtractOptions) (modOptCoreRequires options)
    extractionLanguage <- envString "PROJECT_A_EXTRACTION_LANGUAGE" (modOptExtractionLanguage defaultModExtractOptions) (modOptExtractionLanguage options)
    extractionSupport <- envString "PROJECT_A_EXTRACTION_SUPPORT" (modOptExtractionSupport defaultModExtractOptions) (modOptExtractionSupport options)
    extractionBlacklist <- envList "PROJECT_A_EXTRACTION_BLACKLIST" (modOptExtractionBlacklist defaultModExtractOptions) (modOptExtractionBlacklist options)
    graTerm <- envString "PROJECT_A_BACKEND_GRA" (modOptGraTerm defaultModExtractOptions) (modOptGraTerm options)
    coqFile <- envMaybe "PROJECT_A_COQ_FILE" (modOptCoqFile options)
    requires <- envList "PROJECT_A_EXTRACT_REQUIRE" (modOptRequires defaultModExtractOptions) (modOptRequires options)
    modTerm <- envString "PROJECT_A_EXTRACT_MOD" (modOptModTerm defaultModExtractOptions) (modOptModTerm options)
    resourceTerm <- envString "PROJECT_A_EXTRACT_RESOURCE" (modOptResourceTerm defaultModExtractOptions) (modOptResourceTerm options)
    argTerm <- envString "PROJECT_A_EXTRACT_ARG" (modOptArgTerm defaultModExtractOptions) (modOptArgTerm options)
    outputFile <- envString "PROJECT_A_EXTRACT_OUTPUT" (modOptOutputFile defaultModExtractOptions) (modOptOutputFile options)
    let derivedBackendRoot = deriveBackendRoot toolRoot backendRoot
    let derivedOpamEnvDir = deriveOpamEnvDir toolRoot opamEnvDir
    let derivedCoqProjectFiles = deriveCoqProjectFiles toolRoot coqProjectFiles
    return $ options
        { modOptWorkDir = workDir
        , modOptBackendRoot = derivedBackendRoot
        , modOptToolRoot = toolRoot
        , modOptCoqcCommand = coqcCommand
        , modOptOpamEnvDir = derivedOpamEnvDir
        , modOptCoqExtraArgs = coqExtraArgs
        , modOptCoqProjectFiles = derivedCoqProjectFiles
        , modOptBackendLogical = backendLogical
        , modOptBackendLoadDirs = backendLoadDirs
        , modOptProjectLogical = projectLogical
        , modOptCoreRequires = coreRequires
        , modOptExtractionLanguage = extractionLanguage
        , modOptExtractionSupport = extractionSupport
        , modOptExtractionBlacklist = extractionBlacklist
        , modOptGraTerm = graTerm
        , modOptCoqFile = coqFile
        , modOptRequires = requires
        , modOptModTerm = modTerm
        , modOptResourceTerm = resourceTerm
        , modOptArgTerm = argTerm
        , modOptOutputFile = outputFile
        }

deriveBackendRoot :: Maybe FilePath -> FilePath -> FilePath
deriveBackendRoot Nothing backendRoot = backendRoot
deriveBackendRoot (Just toolRoot) backendRoot
    | backendRoot == modOptBackendRoot defaultModExtractOptions = toolRoot </> "__PROJECT_A_BOOT_STACK_DIR__" </> "__PROJECT_A_BOOT_BACKEND_DIR__"
    | otherwise = backendRoot

deriveOpamEnvDir :: Maybe FilePath -> Maybe FilePath -> Maybe FilePath
deriveOpamEnvDir Nothing current = current
deriveOpamEnvDir (Just toolRoot) Nothing = Just toolRoot
deriveOpamEnvDir _ current = current

deriveCoqProjectFiles :: Maybe FilePath -> [FilePath] -> [FilePath]
deriveCoqProjectFiles Nothing files = files
deriveCoqProjectFiles (Just toolRoot) [] = [toolRoot </> "_CoqProject"]
deriveCoqProjectFiles _ files = files

envString :: String -> String -> String -> IO String
envString key fallback current
    | current /= fallback = return current
    | otherwise = maybe current id <$> lookupEnv key

envList :: String -> [String] -> [String] -> IO [String]
envList key fallback current
    | current /= fallback = return current
    | otherwise = maybe current commaWords <$> lookupEnv key

envMaybe :: String -> Maybe String -> IO (Maybe String)
envMaybe key current
    = case current of
        Just _ -> return current
        Nothing -> lookupEnv key

modConfigFromOptions :: ModExtractOptions -> ModExtractConfig
modConfigFromOptions options = defaultModExtractConfig
    { mecBackendRoot = modOptBackendRoot options
    , mecToolRoot = modOptToolRoot options
    , mecCoqcCommand = modOptCoqcCommand options
    , mecOpamEnvDir = modOptOpamEnvDir options
    , mecCoqExtraArgs = modOptCoqExtraArgs options
    , mecCoqProjectFiles = modOptCoqProjectFiles options
    , mecBackendLogical = modOptBackendLogical options
    , mecBackendLoadDirs = modOptBackendLoadDirs options
    , mecProjectLogical = modOptProjectLogical options
    , mecCoreRequireModules = modOptCoreRequires options
    , mecExtractionLanguage = modOptExtractionLanguage options
    , mecExtractionSupportModule = modOptExtractionSupport options
    , mecExtractionBlacklist = modOptExtractionBlacklist options
    , mecGraTerm = modOptGraTerm options
    , mecCoqFile = modOptCoqFile options
    , mecRequireModules = modOptRequires options
    , mecModTerm = modOptModTerm options
    , mecResourceTerm = modOptResourceTerm options
    , mecArgTerm = modOptArgTerm options
    , mecOutputFile = modOptOutputFile options
    }

withStoredSeed :: String -> Options -> (FilePath -> StoredSeed -> IO ()) -> IO ()
withStoredSeed commandName options action
    = case optCaseDir options of
        Nothing -> putStrLn (commandName ++ "-error: --case-dir=DIR is required")
        Just caseDir -> do
            loaded <- readStoredSeed caseDir
            case loaded of
                Left err -> putStrLn (commandName ++ "-error: " ++ err)
                Right stored -> action caseDir stored

replayWorkDir :: Options -> FilePath -> FilePath
replayWorkDir options caseDir = maybe (caseDir </> "replay") id (optExplicitWorkDir options)

shrinkWorkDir :: Options -> FilePath -> FilePath
shrinkWorkDir options caseDir = maybe (caseDir </> "shrink-work") id (optExplicitWorkDir options)

resetDirectory :: FilePath -> IO ()
resetDirectory dir = do
    exists <- doesDirectoryExist dir
    when exists (removeDirectoryRecursive dir)

writeShrunkArtifacts :: FilePath -> ShrinkResult -> IO ()
writeShrunkArtifacts dir result = do
    let finalReport = srFinalReport result
    let program = tcProgram (crTestCase finalReport)
    createDirectoryIfMissing True dir
    writeTextFile (dir </> "gofile.go") (prettyProgram program)
    writeTextFile (dir </> "feature.json") (featureJson (featuresOf program))
    writeTextFile (dir </> "result.json") (caseReportJson finalReport)
    writeTextFile (dir </> "report.txt") (shrinkReport result)

shrinkReport :: ShrinkResult -> String
shrinkReport result = shrinkReport' result ""

shrinkReport' :: ShrinkResult -> ShowS
shrinkReport' result = strcat
    [ strstr "original-status: " . shows (crStatus original) . nl
    , strstr "shrunk-status: " . shows (crStatus final) . nl
    , strstr "original-objective: " . strstr (programObjectiveText (tcProgram (crTestCase original))) . nl
    , strstr "shrunk-objective: " . strstr (programObjectiveText (tcProgram (crTestCase final))) . nl
    , strstr "objective-drop: " . strstr (programObjectiveDeltaText (tcProgram (crTestCase original)) (tcProgram (crTestCase final))) . nl
    , strstr "original-nodes: " . shows (programNodeCount (tcProgram (crTestCase original))) . nl
    , strstr "shrunk-nodes: " . shows (programNodeCount (tcProgram (crTestCase final))) . nl
    , strstr "tested: " . shows (srTested result) . nl
    , strstr "accepted: " . shows (srAccepted result) . nl
    , strstr "final-case-dir: " . strstr (crCaseDir final) . nl
    ]
    where
        original = srOriginalReport result
        final = srFinalReport result

configFromOptions :: Options -> RunConfig
configFromOptions options = defaultRunConfig { cfgWorkDir = optWorkDir options }

helpText :: String
helpText = helpText' ""

helpText' :: ShowS
helpText' = strcat
    [ strstr "Project A differential fuzzing" . nl
    , nl
    , strstr "Commands:" . nl
    , strstr "  one  --seed=N --size=N --workdir=DIR" . nl
    , strstr "  fuzz --cases=N --seed=N --size=N --workdir=DIR" . nl
    , strstr "  print-go --cases=N --seed=N --size=N" . nl
    , strstr "  search --cases=N --seed=N --size=N --workdir=DIR" . nl
    , strstr "  replay --case-dir=DIR [--workdir=DIR]" . nl
    , strstr "  shrink --case-dir=DIR [--workdir=DIR]" . nl
    , strstr "  mod-extract --mod=TERM [--tool-root=DIR] [--coqproject=FILE] [--opam-env-dir=DIR] [--backend-root=DIR] [--coqc=COQC] [--coq-file=FILE] [--require=M1,M2] [--backend-logical=NAME] [--backend-dirs=D1,D2] [--gra=TERM] [--resource=TERM] [--arg=TERM] [--output=FILE]" . nl
    , strstr "  mod-extract also reads PROJECT_A_TOOL_ROOT, PROJECT_A_OPAM_ENV_DIR, PROJECT_A_COQPROJECTS, PROJECT_A_BACKEND_ROOT, PROJECT_A_COQC, PROJECT_A_EXTRACT_MOD, PROJECT_A_EXTRACT_REQUIRE." . nl
    , nl
    , strstr "The Coq/extraction path is enabled by PROJECT_A_TRANSLATOR." . nl
    , strstr "The translator command must read gofile.go and write generated Coq to stdout." . nl
    ]
