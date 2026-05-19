module TEST.Main (main) where

import Control.Concurrent (forkIO)
import Data.Char (isSpace)
import Data.List (isPrefixOf)
import System.Process
import System.Exit
import System.Directory (getCurrentDirectory)
import System.Environment (getEnvironment)
import System.IO
import Z.System

trim :: String -> String
trim = f . f where
    f = reverse . dropWhile isSpace

streamOutput :: String -> Handle -> IO ()
streamOutput prefix h = do
    eof <- hIsEOF h
    if eof then
        return ()
    else do
        line <- hGetLine h
        putStrLn $ prefix ++ line
        streamOutput prefix h

smoke :: IO ()
smoke = do
    hSetBuffering stdout NoBuffering
    hSetBuffering stderr NoBuffering
    rawPath <- readProcess "stack" ["path", "--project-root"] ""
    let targetDir = trim rawPath
    shelly ("TEST >>= run (\"cd " ++ targetDir ++ " && bash test/smoke.sh\")")
    let innerCmd = "unset GHC_PACKAGE_PATH GHC_ENVIRONMENT STACK_YAML && bash test/smoke.sh"
    let cmd = "script -q -e -c '" ++ innerCmd ++ "' /dev/null"
    let bashProc = (proc "bash" ["-c", cmd]) { cwd = Just targetDir, std_out = Inherit, std_err = Inherit }     
    (_, _, _, ph) <- createProcess bashProc
    exitCode <- waitForProcess ph
    case exitCode of
        ExitSuccess -> do
            shelly ("TEST.smoke> test passed.")
            shelly ("TEST =<< quit")
            exitSuccess
        ExitFailure code -> do
            shelly ("TEST.smoke> FAIL: exit_code=" ++ shows code ".")
            exitFailure

main :: IO ()
main = smoke
