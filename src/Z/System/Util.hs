module Z.System.Util where

import Data.Ratio
import qualified System.Time.Extra as Extra

sleep :: Integer -> IO ()
sleep = Extra.sleep . tomills where
    tomills :: Integer -> Double
    tomills ms = fromRational (ms % 1000)
