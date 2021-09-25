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
    putStrLn ""
    case command of
        "" -> putStrLn "ppap> Quit.\n"
        "Aladdin" -> do
            cout << "ppap> Eval (Aladdin.main).\n" << endl
            Aladdin.main
        "LGS" -> do
            cout << "ppap> Eval (LGS.main).\n" << endl
            LGS.main
        "LGS --default" -> do
            cout << "ppap> Eval (LGS.runLGS \"src/Aladdin/Front/Analyzer/Lexer\").\n" << endl
            LGS.runLGS "src/Aladdin/Front/Analyzer/Lexer"
            putStrLn "ppap> Quit.\n"
        "PGS" -> do
            cout << "ppap> Eval (PGS.main).\n" << endl
            PGS.main
        "PGS --default" -> do
            cout << "ppap> Eval (PGS.runPGS \"src/Aladdin/Front/Analyzer/Parser\").\n" << endl
            PGS.runPGS "src/Aladdin/Front/Analyzer/Parser"
            putStrLn "ppap> Quit.\n"
        "TEST" -> do
            cout << "ppap> Eval (TEST.main).\n" << endl
            TEST.main
        invalid_command -> do
            cout << "ppap> Print (invalid-command=" << show invalid_command << ").\n" << endl
            putStrLn "ppap> Quit.\n"

main :: IO ()
main = ppap
