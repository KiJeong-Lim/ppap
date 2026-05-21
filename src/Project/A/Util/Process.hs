module Project.A.Util.Process where

import Control.Concurrent
import Control.Exception
import System.Environment
import System.Exit
import System.IO
import System.Process
import System.Timeout

import Project.A.Types

data TimedProcessResult = TimedProcessResult
    { tprCommand :: String
    , tprExitCode :: Maybe ExitCode
    , tprTimedOut :: Bool
    , tprStdout :: String
    , tprStderr :: String
    } deriving (Eq, Show)

runTimedProcess :: Int -> Maybe FilePath -> [(String, String)] -> FilePath -> [String] -> String -> IO TimedProcessResult
runTimedProcess timeoutMicros cwd envOverrides command args input = do
    processEnv <- makeProcessEnv envOverrides
    (Just hin, Just hout, Just herr, ph) <- createProcess (proc command args) { cwd = cwd, env = processEnv, std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
    hSetEncoding hin char8
    hSetEncoding hout char8
    hSetEncoding herr char8
    hPutStr hin input
    hClose hin
    outVar <- newEmptyMVar
    errVar <- newEmptyMVar
    _ <- forkIO (readPipe hout >>= putMVar outVar)
    _ <- forkIO (readPipe herr >>= putMVar errVar)
    waited <- timeout timeoutMicros (waitForProcess ph)
    exitCode <- case waited of
        Just code -> return (Just code)
        Nothing -> do
            terminateProcess ph
            _ <- waitForProcess ph
            return Nothing
    out <- takeMVar outVar
    err <- takeMVar errVar
    return TimedProcessResult { tprCommand = unwords (command : args), tprExitCode = exitCode, tprTimedOut = maybe True (const False) exitCode, tprStdout = out, tprStderr = err }

readPipe :: Handle -> IO String
readPipe h = catch go handleReadError where
    go = do
        str <- hGetContents h
        _ <- evaluate (length str)
        return str

handleReadError :: SomeException -> IO String
handleReadError _ = return ""

processLog :: TimedProcessResult -> ProcessLog
processLog result = ProcessLog { plCommand = tprCommand result, plExitCode = fmap exitCodeNumber (tprExitCode result), plTimedOut = tprTimedOut result, plStdout = tprStdout result, plStderr = tprStderr result }

processSucceeded :: TimedProcessResult -> Bool
processSucceeded result
    = case tprExitCode result of
        Just ExitSuccess -> True
        _ -> False

obsFromProcess :: TimedProcessResult -> Obs
obsFromProcess result = Obs { obsTermination = termination, obsExitCode = fmap exitCodeNumber (tprExitCode result), obsStdout = tprStdout result, obsTimedOut = tprTimedOut result } where
    termination
        | tprTimedOut result = TimedOut
        | tprExitCode result == Just ExitSuccess = Terminated
        | otherwise = RuntimeFailed

makeProcessEnv :: [(String, String)] -> IO (Maybe [(String, String)])
makeProcessEnv [] = return Nothing
makeProcessEnv overrides = do
    base <- getEnvironment
    let keys = map fst overrides
    let inherited = filter (\(key, _) -> key `notElem` keys) base
    return (Just (overrides ++ inherited))
