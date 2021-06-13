module Main where

import Z.Utils

main :: IO ()
main = do
    cout << "Hello world!" << endl
    cout << (int)1234 << ' ' << (int)5678 << endl
    return ()
