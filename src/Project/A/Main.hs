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
import Project.A.Pipeline.TestItrExtraction
import Project.A.Pipeline.Runner
import Project.A.Types
import qualified Z.Doc as Doc
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
        TestItrExtract options -> runTestItrExtract options

data Command
    = Help
    | One Options
    | Fuzz Options
    | PrintGo Options
    | Search Options
    | Replay Options
    | Shrink Options
    | ModExtract ModExtractOptions
    | TestItrExtract TestItrExtractOptions
    deriving (Eq, Ord, Show)

data TestItrExtractOptions
    = TestItrExtractOptions
    { testItrOptModOptions :: ModExtractOptions
    , testItrOptTerm :: String
    , testItrOptGhcCommand :: FilePath
    , testItrOptBinaryFile :: FilePath
    } deriving (Eq, Ord, Show)

defaultTestItrExtractOptions :: TestItrExtractOptions
defaultTestItrExtractOptions = TestItrExtractOptions
    { testItrOptModOptions = defaultModExtractOptions { modOptWorkDir = ".project-a-test-itr-extract", modOptModTerm = "", modOptOutputFile = "ExtractedMain.hs"}
    , testItrOptTerm = tieTerm defaultTestItrExtractConfig
    , testItrOptGhcCommand = tieGhcCommand defaultTestItrExtractConfig
    , testItrOptBinaryFile = tieBinaryFile defaultTestItrExtractConfig
    }

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
        "test-itr-extract" : rest -> TestItrExtract (parseTestItrExtractOptions rest)
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

parseTestItrExtractOptions :: [String] -> TestItrExtractOptions
parseTestItrExtractOptions args = defaultTestItrExtractOptions
    { testItrOptModOptions = (parseModExtractOptions args) { modOptWorkDir = stringOption "workdir" (modOptWorkDir (testItrOptModOptions defaultTestItrExtractOptions)) args, modOptCoqFile = testItrCoqFileArg args, modOptModTerm = "", modOptOutputFile = stringOption "output" (modOptOutputFile (testItrOptModOptions defaultTestItrExtractOptions)) args}
    , testItrOptTerm = stringOption "term" (testItrOptTerm defaultTestItrExtractOptions) args
    , testItrOptGhcCommand = stringOption "ghc" (testItrOptGhcCommand defaultTestItrExtractOptions) args
    , testItrOptBinaryFile = stringOption "binary" (testItrOptBinaryFile defaultTestItrExtractOptions) args
    }

testItrCoqFileArg :: [String] -> Maybe FilePath
testItrCoqFileArg args
    = case stringOptionMaybe "coq-file" args of
        Just path -> Just path
        Nothing -> lastMaybe [arg | arg <- map normalizeArg args, ".v" `isSuffixOf` arg, not ("-" `isPrefixOf` arg)]

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just (last xs)

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
    columns <- outputColumns
    putStr (renderCaseReport columns report)

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
        columns <- outputColumns
        putStr (renderCaseReport columns report)

renderCaseReport :: Int -> CaseReport program -> String
renderCaseReport columns report = unlines $
    [ "case-dir: " ++ crCaseDir report
    , "status: " ++ caseStatusText (crStatus report)
    , "result: " ++ pipelineResultText (crResult report)
    ] ++ pipelineResultDetails columns (crResult report)

caseStatusText :: CaseStatus -> String
caseStatusText CasePass = "PASS"
caseStatusText CaseDiscard = "DISCARD"
caseStatusText CaseInconclusive = "INCONCLUSIVE"
caseStatusText (CaseFail failure) = "FAIL (" ++ failureText failure ++ ")"

failureText :: Failure -> String
failureText TranslatorCompletenessBug = "translator"
failureText IllTypedGeneratedCoq = "coq"
failureText ExtractionSetupBug = "extraction"
failureText HaskellRuntimeIntegrationBug = "haskell-runtime-integration"
failureText (ObservableMismatch _ _) = "observable-mismatch"
failureText (TerminationMismatch _ _) = "termination-mismatch"

pipelineResultText :: PipelineResult -> String
pipelineResultText (InvalidGo _) = "InvalidGo"
pipelineResultText (TranslatorError _) = "TranslatorError"
pipelineResultText (CoqError _) = "CoqError"
pipelineResultText (ExtractionError _) = "ExtractionError"
pipelineResultText (HaskellCompileError _) = "HaskellCompileError"
pipelineResultText (NativeRunError _) = "NativeRunError"
pipelineResultText (ExtractedRunError _) = "ExtractedRunError"
pipelineResultText (RanBoth _ _) = "RanBoth"

pipelineResultDetails :: Int -> PipelineResult -> [String]
pipelineResultDetails _ (InvalidGo logValue) =
    [ "stage: native go build"
    , "exit-code: " ++ maybe "-" show (plExitCode logValue)
    ]
pipelineResultDetails columns (TranslatorError message) =
    [ "stage: translator"
    , "message: " ++ oneLine (messageLimit columns) message
    ]
pipelineResultDetails _ (CoqError logValue) =
    [ "stage: coqc"
    , "exit-code: " ++ maybe "-" show (plExitCode logValue)
    ]
pipelineResultDetails columns (ExtractionError message) =
    [ "stage: extraction"
    , "message: " ++ oneLine (messageLimit columns) message
    ]
pipelineResultDetails _ (HaskellCompileError logValue) =
    [ "stage: ghc"
    , "exit-code: " ++ maybe "-" show (plExitCode logValue)
    ]
pipelineResultDetails columns (NativeRunError obsGo) =
    [ "comparison:"
    , renderObsComparison columns obsGo timeoutObs
    ]
pipelineResultDetails columns (ExtractedRunError obsHs) =
    [ "comparison:"
    , renderObsComparison columns timeoutObs obsHs
    ]
pipelineResultDetails columns (RanBoth obsGo obsHs) =
    [ "comparison:"
    , renderObsComparison columns obsGo obsHs
    ]

renderObsComparison :: Int -> Obs -> Obs -> String
renderObsComparison columns obsGo obsHs = renderTable
    [ ["field", "native Go", "extracted Hs"]
    , ["termination", show (obsTermination obsGo), show (obsTermination obsHs)]
    , ["exit-code", maybe "-" show (obsExitCode obsGo), maybe "-" show (obsExitCode obsHs)]
    , ["timed-out", show (obsTimedOut obsGo), show (obsTimedOut obsHs)]
    , ["stdout", oneLine stdoutLimit (show (obsStdout obsGo)), oneLine stdoutLimit (show (obsStdout obsHs))]
    ]
    where
        stdoutLimit = stdoutCellLimit columns

outputColumns :: IO Int
outputColumns = do
    explicit <- lookupEnv "PROJECT_A_OUTPUT_COLUMNS"
    terminal <- lookupEnv "COLUMNS"
    return (maybe defaultOutputColumns (max minimumOutputColumns) (parseColumns explicit `orElse` parseColumns terminal))

defaultOutputColumns :: Int
defaultOutputColumns = 100

minimumOutputColumns :: Int
minimumOutputColumns = 40

parseColumns :: Maybe String -> Maybe Int
parseColumns value =
    case value >>= readMaybeInt of
        Just n | n > 0 -> Just n
        _ -> Nothing

orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing y = y

messageLimit :: Int -> Int
messageLimit columns = max 20 (columns - length "message: ")

stdoutCellLimit :: Int -> Int
stdoutCellLimit columns = max minimumCellWidth ((columns - frameWidth - fieldWidth) `div` 2)
    where
        frameWidth = 10
        fieldWidth = length "termination"
        minimumCellWidth = length "extracted Hs"

renderTable :: [[String]] -> String
renderTable [] = ""
renderTable rows@(header : body) = Doc.renderDoc (Doc.vcat ([ruleDoc, renderHeader header, ruleDoc] ++ map renderBody body ++ [ruleDoc])) where
    widths = columnWidths rows
    ruleDoc = Doc.text ("+" ++ intercalate "+" [replicate (width + 2) '-' | width <- widths] ++ "+")
    renderHeader = renderRow (\width cell -> Doc.textbf (padRight width cell))
    renderBody = renderRow (\width cell -> Doc.text (padRight width cell))
    renderRow renderCell cells = Doc.hcat ([Doc.text "| "] ++ intersperse (Doc.text " | ") (zipWith renderCell widths cells) ++ [Doc.text " |"])

columnWidths :: [[String]] -> [Int]
columnWidths [] = []
columnWidths rows
    | any null rows = []
    | otherwise = maximum (map (length . head) rows) : columnWidths (map tail rows)

padRight :: Int -> String -> String
padRight width str = str ++ replicate (max 0 (width - length str)) ' '

oneLine :: Int -> String -> String
oneLine limit str
    | length cleaned <= limit = cleaned
    | limit <= 3 = take limit cleaned
    | otherwise = take (limit - 3) cleaned ++ "..."
    where
        cleaned = map normalize str
        normalize '\n' = ' '
        normalize '\r' = ' '
        normalize '\t' = ' '
        normalize ch = ch

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

runTestItrExtract :: TestItrExtractOptions -> IO ()
runTestItrExtract rawOptions = do
    options <- applyTestItrExtractEnv rawOptions
    case modOptCoqFile (testItrOptModOptions options) of
        Nothing -> putStrLn "test-itr-extract-error: --coq-file=FILE or a positional FILE.v is required"
        Just _ -> do
            let workDir = modOptWorkDir (testItrOptModOptions options)
            resetDirectory (workDir </> "test-itr-extract")
            report <- runTestItrExtraction defaultRunConfig { cfgWorkDir = workDir } (testItrConfigFromOptions options)
            maybe (return ()) (writeProcessLog (tierCaseDir report </> "coq" </> "opam-env.log")) (tierOpamEnvLog report)
            maybe (return ()) (writeProcessLog (tierCaseDir report </> "coq" </> "input.log")) (tierInputLog report)
            maybe (return ()) (writeProcessLog (tierCaseDir report </> "coq" </> "harness.log")) (tierHarnessLog report)
            maybe (return ()) (writeProcessLog (tierCaseDir report </> "coq" </> "extracted" </> "ghc.log")) (tierGhcLog report)
            putStrLn ("case-dir: " ++ tierCaseDir report)
            putStrLn ("harness: " ++ tierHarnessFile report)
            putStrLn ("extracted-target: " ++ tierExtractedFile report)
            case tierResult report of
                Right path -> putStrLn ("binary: " ++ path)
                Left err -> putStrLn ("test-itr-extract-error: " ++ err)

applyTestItrExtractEnv :: TestItrExtractOptions -> IO TestItrExtractOptions
applyTestItrExtractEnv options = do
    shared0 <- applyModExtractEnv (testItrOptModOptions options)
    workDir <- envString "PROJECT_A_WORKDIR" (modOptWorkDir (testItrOptModOptions defaultTestItrExtractOptions)) (modOptWorkDir (testItrOptModOptions options))
    term <- envString "PROJECT_A_TEST_ITR_TERM" (testItrOptTerm defaultTestItrExtractOptions) (testItrOptTerm options)
    ghcCommand <- envString "PROJECT_A_GHC" (testItrOptGhcCommand defaultTestItrExtractOptions) (testItrOptGhcCommand options)
    binaryFile <- envString "PROJECT_A_TEST_ITR_BINARY" (testItrOptBinaryFile defaultTestItrExtractOptions) (testItrOptBinaryFile options)
    let shared = shared0 { modOptWorkDir = workDir }
    return options { testItrOptModOptions = shared, testItrOptTerm = term, testItrOptGhcCommand = ghcCommand, testItrOptBinaryFile = binaryFile}

testItrConfigFromOptions :: TestItrExtractOptions -> TestItrExtractConfig
testItrConfigFromOptions options = defaultTestItrExtractConfig
    { tieModConfig = modConfigFromOptions (testItrOptModOptions options)
    , tieTerm = testItrOptTerm options
    , tieGhcCommand = testItrOptGhcCommand options
    , tieBinaryFile = testItrOptBinaryFile options
    }

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
    return $ options { modOptWorkDir = workDir, modOptBackendRoot = derivedBackendRoot, modOptToolRoot = toolRoot, modOptCoqcCommand = coqcCommand, modOptOpamEnvDir = derivedOpamEnvDir, modOptCoqExtraArgs = coqExtraArgs, modOptCoqProjectFiles = derivedCoqProjectFiles, modOptBackendLogical = backendLogical, modOptBackendLoadDirs = backendLoadDirs, modOptProjectLogical = projectLogical, modOptCoreRequires = coreRequires, modOptExtractionLanguage = extractionLanguage, modOptExtractionSupport = extractionSupport, modOptExtractionBlacklist = extractionBlacklist, modOptGraTerm = graTerm, modOptCoqFile = coqFile, modOptRequires = requires, modOptModTerm = modTerm, modOptResourceTerm = resourceTerm, modOptArgTerm = argTerm, modOptOutputFile = outputFile}

deriveBackendRoot :: Maybe FilePath -> FilePath -> FilePath
deriveBackendRoot Nothing backendRoot = backendRoot
deriveBackendRoot (Just toolRoot) backendRoot
    | backendRoot == modOptBackendRoot defaultModExtractOptions = toolRoot </> "clightplus" </> "CRIS"
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
shrinkReport' result
    = strcat
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
    [ strstr "[Project A] differential fuzzing" . nl
    , nl
    , strstr "Commands:" . nl
    , strstr "  one  --seed=N --size=N --workdir=DIR" . nl
    , strstr "  fuzz --cases=N --seed=N --size=N --workdir=DIR" . nl
    , strstr "  print-go --cases=N --seed=N --size=N" . nl
    , strstr "  search --cases=N --seed=N --size=N --workdir=DIR" . nl
    , strstr "  replay --case-dir=DIR [--workdir=DIR]" . nl
    , strstr "  shrink --case-dir=DIR [--workdir=DIR]" . nl
    , strstr "  mod-extract --mod=TERM [--tool-root=DIR] [--coqproject=FILE] [--opam-env-dir=DIR] [--backend-root=DIR] [--coqc=COQC] [--coq-file=FILE] [--require=M1,M2] [--backend-logical=NAME] [--backend-dirs=D1,D2] [--gra=TERM] [--resource=TERM] [--arg=TERM] [--output=FILE]" . nl
    , strstr "  test-itr-extract [FILE.v] [--coq-file=FILE] [--term=TERM] [--tool-root=DIR] [--coqproject=FILE] [--opam-env-dir=DIR] [--coqc=COQC] [--ghc=GHC] [--require=M1,M2] [--output=FILE] [--binary=FILE]" . nl
    , strstr "  mod-extract also reads PROJECT_A_TOOL_ROOT, PROJECT_A_OPAM_ENV_DIR, PROJECT_A_COQPROJECTS, PROJECT_A_BACKEND_ROOT, PROJECT_A_COQC, PROJECT_A_EXTRACT_MOD, PROJECT_A_EXTRACT_REQUIRE." . nl
    , strstr "  test-itr-extract also reads PROJECT_A_TEST_ITR_TERM, PROJECT_A_GHC, PROJECT_A_TEST_ITR_BINARY, and the same Coq path variables as mod-extract." . nl
    , nl
    , strstr "The Coq/extraction path is enabled by PROJECT_A_TRANSLATOR." . nl
    , strstr "The translator command must read gofile.go and write generated Coq to stdout." . nl
    ]
