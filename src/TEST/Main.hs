module TEST.Main where

import Jasmine.Alpha1.Solver.Presburger.Test
import TEST.Z
import Z.System.Shelly
import Z.Utils

main :: IO ()
main = do
    query <- shelly ("TEST =<< ")
    case query of
        "" -> do
            shelly ("TEST >>= quit")
            return ()
        "Presburger" -> do
            shelly ("TEST >>= eval (TEST.testPresburger)")
            testPresburger
            shelly ("TEST >>= quit")
            return ()
        "Z" -> do
            shelly ("TEST >>= exec (TEST.testZ)")
            testZ
        invalid_query -> do
            shelly ("TEST >>= tell (invalid-query=" ++ shows invalid_query ")")
            shelly ("TEST >>= quit")
            return ()
