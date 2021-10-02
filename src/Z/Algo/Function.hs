module Z.Algo.Function where

import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infix 9 />

type ErrMsgM = Either String

class TransErr a where
    tryWith :: a -> a -> a

instance TransErr (Maybe a) where
    tryWith (Nothing) = id
    tryWith x = const x

instance TransErr (Either e a) where
    tryWith (Left _) = id
    tryWith x = const x

instance TransErr [a] where
    tryWith xs ys = if null xs then ys else xs

recNat :: Int -> a -> (Int -> a -> a) -> a
recNat n init step = foldr step init (reverse [0 .. n - 1])

(&) :: a -> (a -> b) -> b
(&) = (Function.&)

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromErrMsgM :: HasCallStack => ErrMsgM a -> a
fromErrMsgM = either error id

addErrMsg :: String -> Maybe a -> ErrMsgM a
addErrMsg str = Maybe.maybe (Left str) Right

(/>) :: TransErr a => a -> a -> a
x /> y = tryWith x y

safehd :: [a] -> Maybe a
safehd = foldr (const . Just) Nothing . take 1
