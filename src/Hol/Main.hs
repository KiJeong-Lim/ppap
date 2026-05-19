module Hol.Main where

import Hol.ALPHA2.Main as ALPHA2
import Hol.BETA1.Main as BETA1
import Hol.BETA2.Main as BETA2
import Hol.V1.Main as V1

main :: IO ()
main = BETA2.main

mainWithArgs :: [String] -> IO ()
mainWithArgs = BETA2.mainWithArgs
