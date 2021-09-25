module TEST.Main where

import TEST.Z
import Z.Utils

main :: IO ()
main = do
    cout << "TEST<<< "
    query <- getLine
    case query of
        "" -> return ()
        "Z" -> do
            cout << "TEST> call (testZ)." << endl
            testZ
        invalid_query -> do
            cout << "TEST> tell (invalid-query=" << show invalid_query << ")." << endl
            return ()
    putStrLn "TEST> quit."
