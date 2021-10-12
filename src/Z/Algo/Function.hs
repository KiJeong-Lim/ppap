module Z.Algo.Function where

import Control.Monad
import Control.Monad.Trans.Except
import qualified Data.Foldable as Foldable
import qualified Data.Maybe as Maybe
import GHC.Stack

infixr 3 />

type MyNat = Integer

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

(/>) :: Failable a => a -> a -> a
x /> y = alt x y

takeFirst :: FailableZero b => (a -> b) -> [a] -> b
takeFirst f = foldr alt nil . map f

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromErrMsgM :: HasCallStack => ErrMsgM a -> a
fromErrMsgM = either error id

addErrMsg :: String -> Maybe a -> ErrMsgM a
addErrMsg str = Maybe.maybe (Left str) Right

liftErrMsgM :: Monad m => ErrMsgM a -> ExceptT String m a
liftErrMsgM = ExceptT . return

safehd :: [a] -> Maybe a
safehd = takeFirst Just

recNat :: (Num nat, Enum nat) => a -> (nat -> a -> a) -> nat -> a
recNat my_init my_step n = foldr my_step my_init [n - 1, n - 2 .. 0]

kconcat :: (Foldable.Foldable t, Monad m) => t (a -> m a) -> (a -> m a)
kconcat = Foldable.foldr (>=>) return

cpairing :: MyNat -> (MyNat, MyNat)
cpairing = recNat (0, 0) (\n -> \prev -> if fst prev == 0 then (snd prev + 1, 0) else (fst prev - 1, snd prev + 1))
