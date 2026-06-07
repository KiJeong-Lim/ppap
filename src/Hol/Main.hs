module Hol.Main where

import Hol.ALPHA2.Main as ALPHA2
import Hol.BETA.Main as BETA
import Hol.V1.Main as V1
import qualified Z.System.Shelly

main :: IO ()
main = BETA.main

mainWithArgs :: [String] -> IO ()
mainWithArgs = BETA.mainWithArgs

mainWithArgsM :: [String] -> Z.System.Shelly.ShellyT ()
mainWithArgsM = BETA.mainWithArgsM
