module TEST.Main where

import Jasmine.Main
import TEST.Z
import Z.System.Shelly
import Z.Utils

main :: IO ()
main = do
    query <- shelly "TEST =<< "
    case query of
        "" -> do
            shelly "TEST >>= quit"
            return ()
        "Jasmine" -> do
            shelly "TEST >>= eval (TEST.Jasmine)"
            mapM testJasmine [1, 2, 3, 4, 5, 6, 7]
            shelly "TEST >>= quit"
            return ()
        "Z" -> do
            shelly "TEST >>= exec (TEST.testZ)"
            testZ
        invalid_query -> do
            shelly ("TEST >>= tell (invalid-query=" ++ show invalid_query ++ ")")
            shelly "TEST >>= quit"
            return ()
