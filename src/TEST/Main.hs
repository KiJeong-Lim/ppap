module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    shelly "TEST<<< "
    query <- getLine
    case query of
        "" -> return ()
        "Z" -> do
            shelly "TEST> call (testZ)."
            testZ
        invalid_query -> do
            shelly ("TEST> said (invalid-query=" ++ show invalid_query ++ ").")
            return ()
    shelly "TEST> quit."
