module Main where

import qualified Aladdin.Main as Aladdin
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import qualified TEST.Main as TEST
import Z.Utils

showCopyright :: String
showCopyright = concat
    [ "Copyright (c) 2020-2021, Kijeong Lim\n"
    , "All rights reserved.\n"
    ]

ppap :: IO ()
ppap = do
    cout << "ppap<<< "
    command <- getLine
    case command of
        "" -> putStrLn "ppap> Quit."
        "Aladdin" -> do
            cout << "ppap> Eval (Aladdin.main)." << endl
            Aladdin.main
        "LGS" -> do
            cout << "ppap> Eval (LGS.main)." << endl
            LGS.main
        "LGS --default" -> do
            cout << "ppap> Eval (LGS.runLGS \"src/Aladdin/Front/Analyzer/Lexer\")." << endl
            LGS.runLGS "src/Aladdin/Front/Analyzer/Lexer"
            putStrLn "ppap> Quit."
        "PGS" -> do
            cout << "ppap> Eval (PGS.main)" << endl
            PGS.main
        "PGS --default" -> do
            cout << "ppap> Eval (PGS.runPGS \"src/Aladdin/Front/Analyzer/Parser\")." << endl
            PGS.runPGS "src/Aladdin/Front/Analyzer/Parser"
            putStrLn "ppap> Quit."
        "TEST" -> do
            cout << "ppap> Eval (TEST.main)." << endl
            TEST.main
        invalid_command -> do
            cout << "ppap> Print (invalid-command=" << show invalid_command << ")." << endl
            putStrLn "ppap> Quit."

main :: IO ()
main = ppap
