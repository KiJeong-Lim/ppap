module Calc.Main where

import Calc.Runtime.Executor (runCalc)
import Z.System.Shelly

main :: IO ()
main = do
    dir <- shelly ("Calc =<< ")
    runCalc dir
    shelly ("Calc >>= quit")
    return ()
