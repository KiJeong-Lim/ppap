module Project.A.Main
    ( main
    , mainWithArgs
    ) where

import Control.Monad
import Data.List
import System.Environment

import Project.A.Fuzz.Summary
import Project.A.Pipeline.Config
import Project.A.Pipeline.Runner
import Project.A.Types

main :: IO ()
main = getArgs >>= mainWithArgs

mainWithArgs :: [String] -> IO ()
mainWithArgs args =
    case parseCommand args of
        Help ->
            putStr helpText
        One options ->
            runOne options
        Fuzz options ->
            runFuzz options

data Command
    = Help
    | One Options
    | Fuzz Options
    deriving (Eq, Ord, Show)

data Options = Options
    { optSeed :: Seed
    , optSize :: Size
    , optCases :: Int
    , optWorkDir :: FilePath
    } deriving (Eq, Ord, Show)

defaultOptions :: Options
defaultOptions =
    Options
        { optSeed = 1
        , optSize = 3
        , optCases = 1
        , optWorkDir = cfgWorkDir defaultRunConfig
        }

parseCommand :: [String] -> Command
parseCommand rawArgs =
    case map normalizeArg rawArgs of
        [] -> Help
        "help" : _ -> Help
        "one" : rest -> One (parseOptions rest)
        "fuzz" : rest -> Fuzz (parseOptions rest)
        "--help" : _ -> Help
        unknown : _ ->
            if unknown == "one" || unknown == "--one"
                then One defaultOptions
                else Help

parseOptions :: [String] -> Options
parseOptions args =
    defaultOptions
        { optSeed = intOption "seed" (optSeed defaultOptions) args
        , optSize = intOption "size" (optSize defaultOptions) args
        , optCases = max 1 (intOption "cases" (optCases defaultOptions) args)
        , optWorkDir = stringOption "workdir" (optWorkDir defaultOptions) args
        }

normalizeArg :: String -> String
normalizeArg arg =
    case stripPrefix "--" arg of
        Just rest -> rest
        Nothing -> arg

intOption :: String -> Int -> [String] -> Int
intOption key fallback args =
    case stringOptionMaybe key args >>= readMaybeInt of
        Just n -> n
        Nothing -> fallback

stringOption :: String -> String -> [String] -> String
stringOption key fallback args =
    maybe fallback id (stringOptionMaybe key args)

stringOptionMaybe :: String -> [String] -> Maybe String
stringOptionMaybe key rawArgs =
    go (map normalizeArg rawArgs)
  where
    prefix = key ++ "="

    go [] = Nothing
    go [arg]
        | prefix `isPrefixOf` arg = Just (drop (length prefix) arg)
        | otherwise = Nothing
    go (arg : value : rest)
        | arg == key = Just value
        | prefix `isPrefixOf` arg = Just (drop (length prefix) arg)
        | otherwise = go (value : rest)

readMaybeInt :: String -> Maybe Int
readMaybeInt str =
    case reads str of
        [(n, "")] -> Just n
        _ -> Nothing

runOne :: Options -> IO ()
runOne options = do
    report <- runGeneratedCase (configFromOptions options) 1 (optSeed options) (optSize options)
    putStrLn ("case-dir: " ++ crCaseDir report)
    putStrLn ("status: " ++ show (crStatus report))
    putStrLn ("result: " ++ show (crResult report))

runFuzz :: Options -> IO ()
runFuzz options = do
    summary <- foldM runStep emptySummary [1 .. optCases options]
    putStr (renderSummary summary)
  where
    config = configFromOptions options

    runStep summary caseId = do
        let seed = optSeed options + caseId - 1
        report <- runGeneratedCase config caseId seed (optSize options)
        putStrLn (show caseId ++ ": " ++ show (crStatus report) ++ " " ++ crCaseDir report)
        return (addReport summary report)

configFromOptions :: Options -> RunConfig
configFromOptions options =
    defaultRunConfig { cfgWorkDir = optWorkDir options }

helpText :: String
helpText =
    unlines
        [ "Project A differential fuzzing"
        , ""
        , "Commands:"
        , "  one  --seed=N --size=N --workdir=DIR"
        , "  fuzz --cases=N --seed=N --size=N --workdir=DIR"
        , ""
        , "The Coq/extraction path is enabled by PROJECT_A_TRANSLATOR."
        , "The translator command must read gofile.go and write generated Coq to stdout."
        ]
