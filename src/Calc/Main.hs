module Calc.Main where

import Calc.Runtime.Main
import Control.Monad
import Z.System.File
import Z.System.Path
import Z.System.Shelly

runCalc :: String -> IO ()
runCalc dir = do
    content <- readFileNow dir
    case content of
        Nothing -> putStrLn ("cannot open: " ++ dir)
        Just queries -> do
            runCalculator queries
            return ()

main :: IO ()
main = do
    dir <- shelly "Calc =<< "
    runCalc dir
    shelly "Calc >>= quit"
    return ()
