module Jasmine.Main where

import Jasmine.Alpha1.API (runJasmineAlpha1)
import Z.System.Shelly

main :: IO ()
main = do
    runJasmineAlpha1
    shelly ("Jasmine >>= quit")
    return ()
