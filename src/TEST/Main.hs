module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    shelly "TEST=<< "
    query <- getLine
    case query of
        "" -> shelly "TEST> quit."
        "Z" -> do
            shelly "TEST> exec (TEST.testZ)."
            testZ
        invalid_query -> do
            shelly ("TEST> said (invalid-query=" ++ show invalid_query ++ ").")
            shelly "TEST> quit."
