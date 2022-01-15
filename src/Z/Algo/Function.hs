module Z.Algo.Function where

import Control.Monad
import Control.Monad.Trans.Except
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import qualified Data.Maybe as Maybe
import GHC.Stack
import Z.Utils

infixr 3 />
infixl 1 <^>

type PositiveInteger = Integer

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

instance Failable b => Failable (a -> b) where
    alt = liftM2 alt

instance FailableZero Bool where
    nil = False

instance FailableZero (Maybe a) where
    nil = Nothing

instance FailableZero [a] where
    nil = []

instance FailableZero b => FailableZero (a -> b) where
    nil = const nil

(/>) :: Failable a => a -> a -> a
x /> y = alt x y

takeFirstOf :: FailableZero b => (a -> b) -> [a] -> b
takeFirstOf f = foldr alt nil . map f

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromErrMsgM :: HasCallStack => ErrMsgM a -> a
fromErrMsgM = either error id

addErrMsg :: String -> Maybe a -> ErrMsgM a
addErrMsg str = Maybe.maybe (Left str) Right

liftErrMsgM :: Monad m => ErrMsgM a -> ExceptT String m a
liftErrMsgM = ExceptT . return

safehd :: [a] -> Maybe a
safehd = takeFirstOf Just

recNat :: (Num nat, Enum nat) => (res) -> (nat -> res -> res) -> (nat -> res)
recNat my_init my_step n = foldr my_step my_init [n - 1, n - 2 .. 0]

(<^>) :: (fst1 -> fst2) -> (snd1 -> snd2) -> ((fst1, snd1) -> (fst2, snd2))
map_fst <^> map_snd = pure (curry id) <*> map_fst . fst <*> map_snd . snd

kconcat :: (Foldable.Foldable t, Monad m) => t (a -> m a) -> (a -> m a)
kconcat = Foldable.foldr (>=>) return

mkCantorPair :: (Num nat, Enum nat) => nat -> (nat, nat)
mkCantorPair = recNat (0, 0) (\n -> uncurry $ \x -> \y -> if null [0, 1 .. pred x] then (succ y, 0) else (pred x, succ y))

getGCD :: Integral int => int -> int -> PositiveInteger
getGCD x y
    | negate 1 `elem` map signum [x, y] = Function.on getGCD abs x y
    | 0 `elem` [x, y] = if x == y then error "Z.Algo.Function.getGCD> only zero inputs" else Function.on (+) toInteger x y
    | otherwise = Function.on euclid toInteger x y
    where
        euclid :: MyNat -> MyNat -> PositiveInteger
        euclid a b = case a `mod` b of
            0 -> b
            c -> euclid b c
