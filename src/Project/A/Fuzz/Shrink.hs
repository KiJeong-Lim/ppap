module Project.A.Fuzz.Shrink where

import Control.Monad

import Project.A.Go.AST
import Project.A.Go.Shrink
import Project.A.Pipeline.Config
import Project.A.Pipeline.Runner
import Project.A.Types

data ShrinkResult
    = ShrinkResult
    { srOriginalReport :: CaseReport Program
    , srFinalReport :: CaseReport Program
    , srTested :: Int
    , srAccepted :: Int
    } deriving (Eq, Ord, Show)

runShrinkSearch :: RunConfig -> TestCase Program -> IO ShrinkResult
runShrinkSearch config tc = do
    original <- runCase config (tc { tcCaseId = 1 })
    case crStatus original of
        CaseFail failure -> do
            let target = failureShape failure
            putStrLn "*** Failed! Falsifiable (after 1 test):"
            putStrLn ("failure: " ++ show target)
            putStrLn ("objective: " ++ programObjectiveText (tcProgram (crTestCase original)))
            putStrLn ("case-dir: " ++ crCaseDir original)
            putStrLn "Shrinking..."
            result <- shrinkLoop config target original original [tcProgram (crTestCase original)] 2 0 0
            when (srAccepted result == 0) (putStrLn "  no smaller counterexample found")
            putStrLn (falsifiableSummary result)
            putStrLn ("objective: " ++ programObjectiveText (tcProgram (crTestCase (srFinalReport result))))
            putStrLn ("case-dir: " ++ crCaseDir (srFinalReport result))
            return result
        _ -> return ShrinkResult { srOriginalReport = original, srFinalReport = original, srTested = 0, srAccepted = 0 }

shrinkLoop :: RunConfig -> FailureShape -> CaseReport Program -> CaseReport Program -> [Program] -> CaseId -> Int -> Int -> IO ShrinkResult
shrinkLoop config target original current seen nextId tested accepted = tryCandidates (shrinkProgram currentProgram) seen nextId tested where
    currentProgram = tcProgram (crTestCase current)

    tryCandidates [] _ _ finalTested = return ShrinkResult { srOriginalReport = original, srFinalReport = current, srTested = finalTested, srAccepted = accepted }
    tryCandidates (program : rest) seenSoFar caseId testedSoFar
        | program `elem` seenSoFar = tryCandidates rest seenSoFar caseId testedSoFar
        | not (programImproves currentProgram program) = tryCandidates rest seenSoFar caseId testedSoFar
        | otherwise = do
            candidate <- runCandidate config current caseId program
            let testedNow = testedSoFar + 1
            let seenNow = program : seenSoFar
            let acceptedCandidate = sameFailureShape target (crStatus candidate)
            if acceptedCandidate then do
                putStrLn ("  shrink " ++ show (accepted + 1) ++ ": " ++ programObjectiveDeltaText currentProgram program)
                shrinkLoop config target original candidate seenNow (caseId + 1) testedNow (accepted + 1)
            else
                tryCandidates rest seenNow (caseId + 1) testedNow

runCandidate :: RunConfig -> CaseReport Program -> CaseId -> Program -> IO (CaseReport Program)
runCandidate config current caseId program = runCase config tc where
    old = crTestCase current
    tc = old { tcCaseId = caseId, tcProgram = program, tcSize = programNodeCount program }

programImproves :: Program -> Program -> Bool
programImproves old new = programMeasure new < programMeasure old

programMeasure :: Program -> (Int, Int)
programMeasure program = (programNodeCount program, length (show program))

programObjectiveText :: Program -> String
programObjectiveText program = "nodes=" ++ show nodes ++ ", repr=" ++ show reprLength where
    (nodes, reprLength) = programMeasure program

programObjectiveDeltaText :: Program -> Program -> String
programObjectiveDeltaText old new = concat
    [ "nodes "
    , show oldNodes
    , " -> "
    , show newNodes
    , ", repr "
    , show oldReprLength
    , " -> "
    , show newReprLength
    ]
    where
        (oldNodes, oldReprLength) = programMeasure old
        (newNodes, newReprLength) = programMeasure new

falsifiableSummary :: ShrinkResult -> String
falsifiableSummary result = concat
    [ "*** Failed! Falsifiable (after "
    , show (1 + srTested result)
    , " "
    , plural (1 + srTested result) "test"
    , " and "
    , show (srAccepted result)
    , " "
    , plural (srAccepted result) "shrink"
    , "):"
    ]

plural :: Int -> String -> String
plural 1 word = word
plural _ word = word ++ "s"

data FailureShape
    = ShapeTranslatorCompletenessBug
    | ShapeIllTypedGeneratedCoq
    | ShapeExtractionSetupBug
    | ShapeHaskellRuntimeIntegrationBug
    | ShapeObservableMismatch
    | ShapeTerminationMismatch
    deriving (Eq, Ord, Show)

failureShape :: Failure -> FailureShape
failureShape TranslatorCompletenessBug = ShapeTranslatorCompletenessBug
failureShape IllTypedGeneratedCoq = ShapeIllTypedGeneratedCoq
failureShape ExtractionSetupBug = ShapeExtractionSetupBug
failureShape HaskellRuntimeIntegrationBug = ShapeHaskellRuntimeIntegrationBug
failureShape (ObservableMismatch _ _) = ShapeObservableMismatch
failureShape (TerminationMismatch _ _) = ShapeTerminationMismatch

sameFailureShape :: FailureShape -> CaseStatus -> Bool
sameFailureShape target (CaseFail failure) = target == failureShape failure
sameFailureShape _ _ = False
