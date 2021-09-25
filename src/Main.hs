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
        "" -> return ()
        "Aladdin" -> do
            cout << "ppap> Aladdin.main" << endl
            Aladdin.main
        "LGS" -> do
            cout << "ppap> LGS.main" << endl
            LGS.main
        "LGS --default" -> do
            cout << "ppap> LGS.runLGS \"src/Aladdin/Front/Analyzer/Lexer\"" << endl
            LGS.runLGS "src/Aladdin/Front/Analyzer/Lexer"
            return ()
        "PGS" -> do
            cout << "ppap> PGS.main" << endl
            PGS.main
        "PGS --default" -> do
            cout << "ppap> PGS.runPGS \"src/Aladdin/Front/Analyzer/Parser\"" << endl
            PGS.runPGS "src/Aladdin/Front/Analyzer/Parser"
            return ()
        "TEST" -> do
            cout << "ppap> TEST.main" << endl
            TEST.main
        invalid_command -> do
            cout << "ppap> invalid-command=" << show invalid_command << endl
            return ()

main :: IO ()
main = ppap
