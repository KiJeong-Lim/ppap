module Z.Algo.Function where

import qualified Data.Function as Function

recNat :: Int -> a -> (Int -> a -> a) -> a
recNat n init step = foldr step init (reverse [0 .. n - 1])

(&) :: a -> (a -> b) -> b
(&) = (Function.&)
