module Z.Algo.Function where

import Data.Function

recNat :: Int -> a -> (Int -> a -> a) -> a
recNat n init step = foldr step init (reverse [0 .. n - 1])
