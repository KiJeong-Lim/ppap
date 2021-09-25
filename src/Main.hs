module Main where

import qualified Aladdin.Main as Aladdin
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import qualified Test.Main as Test
import Z.Utils

showCopyright :: String
showCopyright = concat
    [ "Copyright (c) 2020-2021, Kijeong Lim\n"
    , "All rights reserved.\n"
    ]

main :: IO ()
main = do
    putStrLn "ppap"
    command <- getLine
    case command of
        "" -> return ()
        "Aladdin" -> Aladdin.main
        "LGS" -> LGS.main
        "PGS" -> PGS.main
        "Test" -> Test.main
        invalid_command -> do
            cout << "invalid-command = " << show invalid_command << endl
            return ()
