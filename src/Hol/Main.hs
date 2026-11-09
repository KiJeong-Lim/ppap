module Hol.Main where

import qualified Hol.BETA.Main as BETA
import qualified Hol.V1.Main as V1
import qualified Z.System.Shelly

main :: IO ()
main = BETA.main

mainWithArgs :: [String] -> IO ()
mainWithArgs args
    | "v1" `elem` args = V1.mainWithArgs (filter (/= "v1") args)
    | otherwise = BETA.mainWithArgs args

mainWithArgsM :: [String] -> Z.System.Shelly.ShellyT ()
mainWithArgsM args
    | "v1" `elem` args = V1.mainWithArgsM (filter (/= "v1") args)
    | otherwise = BETA.mainWithArgsM args

validArgs :: [String] -> Bool
validArgs args
    | "v1" `elem` args = length (filter (== "v1") args) == 1 && V1.validArgs (filter (/= "v1") args)
    | otherwise = args `elem` [[], ["pretty"], ["test"]]
