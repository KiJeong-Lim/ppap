module Z.Algo.Function where

import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

recNat :: Int -> a -> (Int -> a -> a) -> a
recNat n init step = foldr step init (reverse [0 .. n - 1])

(&) :: a -> (a -> b) -> b
(&) = (Function.&)

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

maybeAlt :: Maybe a -> Maybe a -> Maybe a
maybeAlt (Nothing) y = y
maybeAlt x _ = x
