module Jasmine.Main where

import Jasmine.Alpha1.API
import Z.System.Shelly

main :: IO ()
main = do
    runJasmineAlpha1
    shelly ("Jasmine >>= quit")
    return ()
