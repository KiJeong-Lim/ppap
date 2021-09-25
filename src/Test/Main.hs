module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    cout << "TEST<<< "
    query <- getLine
    case query of
        "" -> return ()
        "Z" -> testZ
        invalid_query -> do
            cout << "TEST> invalid-query=" << show invalid_query << endl
            return ()
