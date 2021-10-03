module Z.Algo.Function where

import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infix 9 />

type ErrMsgM = Either String

class Failable a where
    isNothing :: a -> Bool

class Failable a => FailableZero a where
    myNothing :: a

instance Failable (Maybe a) where
    isNothing = Maybe.isNothing

instance Failable (Either e a) where
    isNothing = either (const True) (const False)

instance Failable [a] where
    isNothing = null

instance FailableZero (Maybe a) where
    myNothing = Nothing

instance FailableZero [a] where
    myNothing = []

recNat :: a -> (Int -> a -> a) -> Int -> a
recNat my_init my_step n = foldr my_step my_init (reverse [0 .. n - 1])

(&) :: a -> (a -> b) -> b
(&) = (Function.&)

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromErrMsgM :: HasCallStack => ErrMsgM a -> a
fromErrMsgM = either error id

addErrMsg :: String -> Maybe a -> ErrMsgM a
addErrMsg str = Maybe.maybe (Left str) Right

(/>) :: Failable a => a -> a -> a
x /> y = if isNothing x then y else x

getFirstMatched :: FailableZero b => (a -> b) -> [a] -> b
getFirstMatched f = foldr (/>) myNothing . map f

safehd :: [a] -> Maybe a
safehd = getFirstMatched Just
