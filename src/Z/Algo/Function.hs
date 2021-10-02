module Z.Algo.Function where

import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infix 9 />

class TransErr a where
    tryWith :: a -> a -> a

instance TransErr (Maybe a) where
    tryWith (Nothing) = id
    tryWith x = const x

instance TransErr (Either e a) where
    tryWith (Left _) = id
    tryWith x = const x

recNat :: Int -> a -> (Int -> a -> a) -> a
recNat n init step = foldr step init (reverse [0 .. n - 1])

(&) :: a -> (a -> b) -> b
(&) = (Function.&)

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromEither :: HasCallStack => Either String a -> a
fromEither = either error id

(/>) :: TransErr a => a -> a -> a
x /> y = tryWith x y

safehd :: [a] -> Maybe a
safehd = foldr (const . Just) Nothing . take 1
