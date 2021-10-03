module Z.Algo.Function where

import Control.Monad
import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack

infixr 3 />

type ErrMsgM = Either String

class Failable a where
    imp :: a -> a -> a

class Failable a => FailableZero a where
    bot :: a

instance Failable Bool where
    imp (False) = id
    imp x = const x

instance Failable (Maybe a) where
    imp (Nothing) = id
    imp x = const x

instance Failable (Either e a) where
    imp (Left _) = id
    imp x = const x

instance Failable [a] where
    imp [] = id
    imp x = const x

instance FailableZero Bool where
    bot = False

instance FailableZero (Maybe a) where
    bot = Nothing

instance FailableZero [a] where
    bot = []

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
x /> y = imp x y

getFirstMatched :: FailableZero b => (a -> b) -> [a] -> b
getFirstMatched f = foldr imp bot . map f

safehd :: [a] -> Maybe a
safehd = getFirstMatched Just

kconcat :: Monad m => [a -> m a] -> a -> m a
kconcat [] = return
kconcat (k : ks) = k >=> kconcat ks
