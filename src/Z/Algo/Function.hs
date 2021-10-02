module Z.Algo.Function where

import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infix 9 />

type ErrMsgM = Either String

class Failable a where
    failed :: a -> Bool

instance Failable (Maybe a) where
    failed = Maybe.isNothing

instance Failable (Either e a) where
    failed = either (const True) (const False)

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

(/>) :: Failable a => a -> a -> a
x /> y = if failed x then y else x

safehd :: [a] -> Maybe a
safehd = foldr (const . Just) Nothing
