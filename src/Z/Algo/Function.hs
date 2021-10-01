module Z.Algo.Function where

import Data.Function
import qualified Data.List as List

foldNat :: Int -> a -> (Int -> a -> a) -> a
foldNat n init step = if n < 0 then undefined else foldr step init (reverse [0 .. n - 1])
