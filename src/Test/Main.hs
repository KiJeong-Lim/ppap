module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    cout << "TEST<<< "
    query <- getLine
    case query of
        "" -> putStrLn "TEST> Quit."
        "Z" -> do
            cout << "TEST> Call (testZ)." << endl
            testZ
        invalid_query -> do
            cout << "TEST> Print (invalid-query=" << show invalid_query << ")." << endl
            putStrLn "TEST> Quit."
