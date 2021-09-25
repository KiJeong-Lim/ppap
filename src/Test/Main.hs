module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    cout << "TEST<<< "
    query <- getLine
    putStrLn ""
    case query of
        "" -> putStrLn "TEST> Quit.\n"
        "Z" -> do
            cout << "TEST> Call (testZ).\n" << endl
            testZ
        invalid_query -> do
            cout << "TEST> Print (invalid-query=" << show invalid_query << ").\n" << endl
            putStrLn "TEST> Quit.\n"
