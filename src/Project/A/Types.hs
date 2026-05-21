module Project.A.Types where

import System.Exit

type Seed = Int

type Size = Int

type CaseId = Int

data RuntimeInput
    = RuntimeInput
    { riArgs :: [String]
    , riStdin :: String
    , riEnv :: [(String, String)]
    } deriving (Eq, Ord, Show)

data TestCase program
    = TestCase
    { tcCaseId :: CaseId
    , tcSeed :: Seed
    , tcSize :: Size
    , tcProgram :: program
    , tcInput :: RuntimeInput
    } deriving (Eq, Ord, Show)

data Termination
    = Terminated
    | TimedOut
    | RuntimeFailed
    deriving (Eq, Ord, Show)

data Obs
    = Obs
    { obsTermination :: Termination
    , obsExitCode :: Maybe Int
    , obsStdout :: String
    , obsTimedOut :: Bool
    } deriving (Eq, Ord, Show)

data ProcessLog
    = ProcessLog
    { plCommand :: String
    , plExitCode :: Maybe Int
    , plTimedOut :: Bool
    , plStdout :: String
    , plStderr :: String
    } deriving (Eq, Ord, Show)

data PipelineResult
    = InvalidGo ProcessLog
    | TranslatorError String
    | CoqError ProcessLog
    | ExtractionError String
    | HaskellCompileError ProcessLog
    | NativeRunError Obs
    | ExtractedRunError Obs
    | RanBoth Obs Obs
    deriving (Eq, Ord, Show)

data Failure
    = TranslatorCompletenessBug
    | IllTypedGeneratedCoq
    | ExtractionSetupBug
    | HaskellRuntimeIntegrationBug
    | ObservableMismatch Obs Obs
    | TerminationMismatch Obs Obs
    deriving (Eq, Ord, Show)

data CaseStatus
    = CasePass
    | CaseDiscard
    | CaseFail Failure
    | CaseInconclusive
    deriving (Eq, Ord, Show)

data CaseReport program
    = CaseReport
    { crCaseDir :: FilePath
    , crTestCase :: TestCase program
    , crResult :: PipelineResult
    , crStatus :: CaseStatus
    } deriving (Eq, Ord, Show)

exitCodeNumber :: ExitCode -> Int
exitCodeNumber ExitSuccess = 0
exitCodeNumber (ExitFailure n) = n

obsEqual :: Obs -> Obs -> Bool
obsEqual lhs rhs = obsTermination lhs == obsTermination rhs && obsExitCode lhs == obsExitCode rhs && obsStdout lhs == obsStdout rhs && obsTimedOut lhs == obsTimedOut rhs

classifyResult :: PipelineResult -> CaseStatus
classifyResult (InvalidGo _)
    = CaseDiscard
classifyResult (TranslatorError _)
    = CaseFail TranslatorCompletenessBug
classifyResult (CoqError _)
    = CaseFail IllTypedGeneratedCoq
classifyResult (ExtractionError _)
    = CaseFail ExtractionSetupBug
classifyResult (HaskellCompileError _)
    = CaseFail HaskellRuntimeIntegrationBug
classifyResult (NativeRunError obs)
    = CaseFail (TerminationMismatch obs timeoutObs)
classifyResult (ExtractedRunError obs)
    = CaseFail (TerminationMismatch timeoutObs obs)
classifyResult (RanBoth obsGo obsHs)
    | obsTimedOut obsGo && obsTimedOut obsHs = CaseInconclusive
    | obsEqual obsGo obsHs = CasePass
    | obsTermination obsGo /= obsTermination obsHs || obsTimedOut obsGo /= obsTimedOut obsHs = CaseFail (TerminationMismatch obsGo obsHs)
    | otherwise = CaseFail (ObservableMismatch obsGo obsHs)

timeoutObs :: Obs
timeoutObs = Obs { obsTermination = TimedOut, obsExitCode = Nothing, obsStdout = "", obsTimedOut = True }
