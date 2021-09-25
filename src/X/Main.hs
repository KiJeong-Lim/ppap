module X.Main where

import X.Z
import Z.Utils

main :: IO ()
main = do
    cout << "TEST<<< "
    query <- getLine
    case query of
        "" -> return ()
        "Z" -> do
            cout << "TEST> Call (testZ)." << endl
            testZ
        invalid_query -> do
            cout << "TEST> Print (invalid-query=" << show invalid_query << ")." << endl
            return ()
    putStrLn "TEST> Quit."
