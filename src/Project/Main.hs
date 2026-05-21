module Project.Main
    ( main
    , mainWithArgs
    ) where

import qualified Project.A.Main as A

main :: IO ()
main = A.main

mainWithArgs :: [String] -> IO ()
mainWithArgs = A.mainWithArgs
