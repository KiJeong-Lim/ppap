module Z.System.Util where

import Data.Ratio
import qualified System.Time.Extra as Extra

sleep :: Integer -> IO ()
sleep = Extra.sleep . fromMilliSec where
    fromMilliSec :: Integer -> Double
    fromMilliSec ms = fromRational (ms % 1000)
