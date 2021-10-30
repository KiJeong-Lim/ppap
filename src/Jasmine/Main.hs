module Jasmine.Main where

import Jasmine.API
import Z.System.Shelly

main :: IO ()
main = do
    runJasmine
    shelly ("Jasmine >>= quit")
    return ()
