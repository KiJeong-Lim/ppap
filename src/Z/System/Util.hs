module Z.System.Util where

import Data.Ratio
import qualified System.Time.Extra as Extra

tomills :: Integer -> Double
tomills ms = fromRational (ms % 1000)

sleep :: Integer -> IO ()
sleep = Extra.sleep . tomills
