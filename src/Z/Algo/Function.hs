module Z.Algo.Function where

import Control.Monad
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infixr 3 />

type ErrMsgM = Either String

class Failable a where
    alt :: a -> a -> a

class Failable a => FailableZero a where
    nil :: a

instance Failable Bool where
    alt (False) = id
    alt x = const x

instance Failable (Maybe a) where
    alt (Nothing) = id
    alt x = const x

instance Failable (Either e a) where
    alt (Left _) = id
    alt x = const x

instance Failable [a] where
    alt [] = id
    alt x = const x

instance FailableZero Bool where
    nil = False

instance FailableZero (Maybe a) where
    nil = Nothing

instance FailableZero [a] where
    nil = []

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
x /> y = alt x y

getFirstMatched :: FailableZero b => (a -> b) -> [a] -> b
getFirstMatched f = foldr alt nil . map f

safehd :: [a] -> Maybe a
safehd = getFirstMatched Just

kconcat :: (Foldable.Foldable t, Monad m) => t (a -> m a) -> (a -> m a)
kconcat = Foldable.foldr (>=>) return
