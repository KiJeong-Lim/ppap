module Main (main) where

import Control.Monad (unless)
import System.Directory (findExecutable, makeAbsolute)
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((</>))
import System.Process (CreateProcess (..), createProcess, proc, waitForProcess)

main :: IO ()
main
    = do
        ppap <- findExecutable "ppap" >>= maybe missingExecutable makeAbsolute
        env0 <- getEnvironment
        (_, _, _, processHandle) <- createProcess $ (proc "bash" ["test" </> "smoke.sh"]) { env = Just (("PPAP_BIN", ppap) : filter ((/= "PPAP_BIN") . fst) env0) }
        result <- waitForProcess processHandle
        unless (result == ExitSuccess) (exitWith result)
    where
        missingExecutable = do
            putStrLn "hol-beta-smoke: Cabal did not put the ppap executable on PATH"
            exitWith (ExitFailure 2)
