module Z.System.Util where

import Data.Ratio
import qualified System.Time.Extra as Extra
import Z.Utils

tomills :: Integer -> Double
tomills ms = fromRational (ms % 1000)

sleep :: Integer -> IO ()
sleep = Extra.sleep . tomills

modifyWithout :: Char -> (String -> String) -> String -> String
modifyWithout ch delta = connect . map delta . splitBy ch where
    connect :: [String] -> String
    connect [] = []
    connect [str] = str
    connect (str : strs) = str ++ [ch] ++ connect strs
