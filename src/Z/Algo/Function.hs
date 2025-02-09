{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Z.Algo.Function where

import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Fix
import Control.Monad.Trans.State.Strict
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import Data.Functor.Identity
import Data.Semigroup
import Data.Kind
import qualified Data.Maybe as Maybe
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Stack
import Z.Utils

infixr 3 />
infixl 1 <^>

type PositiveInteger = Integer

type MyNat = Integer

type ErrMsgM = Either String

class Callable obj where
    type Dom obj :: Type
    type Cod obj :: Type
    call :: HasCallStack => obj -> Dom obj -> Cod obj

class Failable a where
    alt :: a -> a -> a

class Failable a => FailableZero a where
    nil :: a

instance Callable (src -> tgt) where
    type Dom (src -> tgt) = src
    type Cod (src -> tgt) = tgt
    call = ($!)

instance Ord key => Callable (Map.Map key val) where
    type Dom (Map.Map key val) = key
    type Cod (Map.Map key val) = val
    call m k = case k `Map.lookup` m of
        Nothing -> error "call: out of domain"
        Just v -> v

instance Ord elem => Callable (Set.Set elem) where
    type Dom (Set.Set elem) = elem
    type Cod (Set.Set elem) = Bool
    call xs x = x `Set.member` xs

instance (Callable f1, Callable f2) => Callable (f1, f2) where
    type Dom (f1, f2) = (Dom f1, Dom f2)
    type Cod (f1, f2) = (Cod f1, Cod f2)
    call (f1, f2) (x1, x2) = (call f1 x1, call f2 x2)

instance Callable () where
    type Dom () = ()
    type Cod () = ()
    call () () = ()

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

digraph :: forall vertex output. (Ord vertex, Monoid output, HasCallStack) => Set.Set vertex -> (vertex -> vertex -> Bool) -> (vertex -> output) -> Map.Map vertex output
digraph your_X your_R your_F' = Map.map snd (snd (snd (runIdentity (runStateT (mapM_ (go k0) your_X) ([], Map.fromSet (const (0, mempty)) your_X))))) where
    k0 :: Min Int
    k0 = 1
    go :: forall n. (Num n, Enum n, Ord n, Bounded n) => Min n -> vertex -> StateT ([vertex], Map.Map vertex (Min n, output)) Identity ()
    go k x = do
        (stack, _N_F) <- get
        when (fst (_N_F Map.! x) == 0) $ do
            put (x : stack, Map.adjust (const (k, your_F' x)) x _N_F)
            forM_ your_X $ \y -> do
                when (your_R x y) $ do
                    (go $! succ k) y
                    (stack, _N_F) <- get
                    put (stack, Map.adjust (mappend (_N_F Map.! y)) x _N_F)
            (_, _N_F) <- get
            let (xN, xF) = _N_F Map.! x
            when (xN == k) $ do
                Function.fix $ \loop -> do
                    (stack, _N_F) <- get
                    let top = head stack
                    put (tail stack, Map.adjust (const (mempty, xF)) top _N_F)
                    unless (top == x) $ do
                        loop
    digraphTest :: Map.Map Char (Set.Set Char)
    digraphTest = digraph (Set.fromList "abcdef") edge Set.singleton where
        edge 'a' 'b' = True
        edge 'b' 'c' = True
        edge 'c' 'a' = True
        edge 'c' 'd' = True
        edge 'c' 'f' = True
        edge 'e' 'd' = True
        edge _ _ = False
    -- digraphTest = fromList [('a',fromList "abcdf"),('b',fromList "abcdf"),('c',fromList "abcdf"),('d',fromList "d"),('e',fromList "de"),('f',fromList "f")]

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
f1 <^> f2 = call (f1, f2)

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
