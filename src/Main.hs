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
    shelly "ppap<<< "
    command <- getLine
    case command of
        "" -> shelly "ppap> quit."
        "Aladdin" -> do
            shelly "ppap> exec (Aladdin.main)."
            Aladdin.main
        "LGS" -> do
            shelly "ppap> exec (LGS.main)."
            LGS.main
        "LGS --default" -> do
            shelly "ppap> eval (LGS.runLGS \"src/Aladdin/Front/Analyzer/Lexer\")."
            LGS.runLGS "src/Aladdin/Front/Analyzer/Lexer"
            shelly "ppap> quit."
        "PGS" -> do
            shelly "ppap> exec (PGS.main)."
            PGS.main
        "PGS --default" -> do
            shelly "ppap> eval (PGS.runPGS \"src/Aladdin/Front/Analyzer/Parser\")."
            PGS.runPGS "src/Aladdin/Front/Analyzer/Parser"
            shelly "ppap> quit."
        "TEST" -> do
            shelly "ppap> exec (TEST.main)."
            TEST.main
        invalid_command -> do
            shelly ("ppap> said (invalid-command=" ++ show invalid_command ++ ").")
            shelly "ppap> quit."

main :: IO ()
main = ppap
