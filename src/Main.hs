module Main where

import qualified Aladdin.Main as Aladdin
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS

main :: IO ()
main = do
    putStrLn "ppap"
    command <- getLine
    case command of
        "Aladdin" -> Aladdin.main
        "LGS" -> LGS.main
        "PGS" -> PGS.main
        _ -> return ()
