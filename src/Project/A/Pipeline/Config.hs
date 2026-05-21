module Project.A.Pipeline.Config where

data TimeoutConfig
    = TimeoutConfig
    { timeoutGofmt :: Int
    , timeoutGoBuild :: Int
    , timeoutNativeRun :: Int
    , timeoutTranslator :: Int
    , timeoutCoqc :: Int
    , timeoutGhc :: Int
    , timeoutExtractedRun :: Int
    } deriving (Eq, Ord, Show)

data RunConfig
    = RunConfig
    { cfgWorkDir :: FilePath
    , cfgTimeouts :: TimeoutConfig
    } deriving (Eq, Ord, Show)

defaultRunConfig :: RunConfig
defaultRunConfig = RunConfig { cfgWorkDir = ".project-a-work", cfgTimeouts = TimeoutConfig { timeoutGofmt = 1000000, timeoutGoBuild = 2000000, timeoutNativeRun = 1000000, timeoutTranslator = 2000000, timeoutCoqc = 5000000, timeoutGhc = 5000000, timeoutExtractedRun = 1000000 } }
