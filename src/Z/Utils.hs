module Z.Utils where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO

infixl 1 <<

type ErrMsg = String

type Prec = Int

type Nat = Int

type List = []

type Indentation = Int

type Precedence = Int

data Flush
    = Flush
    deriving (Eq, Ord, Show)

newtype UniqueT m a
    = UniqueT { runUniqueT :: StateT Integer m a }
    deriving ()

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord)

class OStreamTrain os where
    getHandleFrom :: os -> IO Handle

class OStreamCargo a where
    hput :: Handle -> a -> IO ()

class Outputable a where
    pprint :: Prec -> a -> ShowS

class HasAnnot f where
    getAnnot :: f a -> a
    setAnnot :: a -> f a -> f a

class Monad m => MonadUnique m where
    getUnique :: m Unique

class IsInt a where
    toInt :: a -> Int
    fromInt :: Int -> a

instance OStreamTrain (Handle) where
    getHandleFrom h = pure h

instance OStreamTrain a => OStreamTrain (IO a) where
    getHandleFrom h = h >>= getHandleFrom

instance OStreamCargo (Char) where
    hput = hPutChar

instance OStreamCargo a => OStreamCargo [a] where
    hput = mapM_ . hput

instance (Monoid a, OStreamCargo b) => OStreamCargo (a -> b) where
    hput h = hput h . withZero

instance OStreamCargo (Flush) where
    hput = const . hFlush

instance OStreamCargo (Int) where
    hput h = hput h . shows

instance OStreamCargo (Integer) where
    hput h = hput h . shows

instance OStreamCargo (Double) where
    hput h = hput h . shows

instance OStreamCargo (Bool) where
    hput h b = hput h (if b then "true" else "false")

withZero :: Monoid a => (a -> b) -> b
withZero to_be_initialized = to_be_initialized mempty

kons :: a -> [a] -> [a]
kons my_hd my_tl = my_hd `seq` my_tl `seq` my_hd : my_tl

cout :: Handle
cout = stdout

cerr :: Handle
cerr = stderr

endl :: Char
endl = '\n'

(<<) :: (OStreamTrain os, OStreamCargo a) => os -> a -> IO Handle
my_ostream << your_cargo = do
    my_handle <- getHandleFrom my_ostream
    hput my_handle your_cargo
    return my_handle

execUniqueT :: Functor m => UniqueT m a -> m a
execUniqueT = fmap fst . flip runStateT 0 . runUniqueT
{-# INLINABLE execUniqueT #-}

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id
{-# INLINABLE strcat #-}

pshow :: Outputable a => a -> String
pshow x = pprint 0 x ""
{-# INLINABLE pshow #-}

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg f x = f $! x

one :: a -> [a]
one = callWithStrictArg pure

modifySep :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySep x0 f1 f2 = f1 x0 & (\zs -> concat . foldr (\ys -> \acc -> if null acc then ys : acc else ys : zs : acc) [] . map f2 . splitBy x0)

nl :: ShowS
nl = showString "\n"

pindent :: Indentation -> ShowS
pindent space = if space < 0 then id else showString (replicate space ' ')

ppunc :: String -> [ShowS] -> ShowS
ppunc str deltas = if null deltas then id else head deltas . foldr (\delta -> \acc -> strstr str . delta . acc) id (tail deltas)

plist' :: Indentation -> [ShowS] -> ShowS
plist' space deltas = nl . pindent space . strstr "[ " . ppunc (withZero (nl . pindent space . strstr ", ")) deltas . nl . pindent space . strstr "]"

plist :: Indentation -> [ShowS] -> ShowS
plist space deltas = if null deltas then strstr "[]" else plist' space deltas

quotify :: ShowS -> ShowS
quotify = shows . withZero

plist1 :: Indentation -> [ShowS] -> ShowS
plist1 space [] = strstr "[]"
plist1 space [delta] = strstr "[" . delta . strstr "]"
plist1 space deltas = plist' space deltas

pprintChar :: Char -> String -> String
pprintChar ch = strstr "\\\'" . pprint 0 ch . strstr "\\\'"

pprintString :: String -> String -> String
pprintString str = strstr "\"" . strcat (map (pprint 0) str) . strstr "\""

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless is_related_to = foldr (\x -> recList [pure x] (\xs -> if x `is_related_to` head xs then const . kons (pure x ++ xs) else const . kons (pure x) . kons xs)) []

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x0 = fix (\swag -> flip (recList (\buffer -> [reverse buffer]) (\x -> \xs -> \go -> \buffer -> if x == x0 then [reverse buffer] ++ swag xs else go (x : buffer))) [])

calcTab :: Int -> Int
calcTab n = 4 & (\my_tab_width -> my_tab_width - n `mod` my_tab_width)

modifySepAlt :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySepAlt = modifySep

findAllPermutationsOf :: [a] -> [[a]]
findAllPermutationsOf = swag (\at -> uncurry $ \i -> \j -> maybe . at <*> curry snd <*> flip lookup [(i, at j), (j, at i)]) . zipWith const [0 ..] <*> (!!) where
    swag :: ((Int -> a) -> (Int, Int) -> (Int -> a)) -> [Int] -> ((Int -> a) -> [[a]])
    swag my_swap all_idxes = foldr (\n -> \kont -> \at -> [0 .. n] >>= kont . curry (my_swap at) n) (\at -> return (map at all_idxes)) all_idxes

recList :: (r) -> (a -> [a] -> r -> r) -> ([a] -> r)
recList for_nil for_cons = snd . foldr (\my_hd -> uncurry $ \my_tl -> \my_result -> (my_hd : my_tl, for_cons my_hd my_tl my_result)) ([], for_nil)

primes :: [Integer]
primes = go [2 .. ] where
    go :: [Integer] -> [Integer]
    go (p : ns) = p : go (filter (\n -> n `mod` p /= 0) ns)

clockwise :: [[a]] -> [[a]]
clockwise = Z.Utils.transpose . reverse

transpose :: [[a]] -> [[a]]
transpose [] = repeat []
transpose (xs : xss) = zipWith (:) xs (Z.Utils.transpose xss)

instance Outputable Char where
    pprint _ = strstr . dispatch where
        dispatch :: Char -> String
        dispatch '\"' = "\\\""
        dispatch '\'' = "\\\'"
        dispatch '\\' = "\\\\"
        dispatch '\t' = "\\t"
        dispatch '\n' = "\\n"
        dispatch '\r' = "\\r"
        dispatch '\f' = "\\f"
        dispatch c = [c]

instance Outputable Integer where
    pprint prec = if prec == 0 then byDigitsOf 3 else shows where
        byDigitsOf :: Int -> Integer -> ShowS
        byDigitsOf k n
            | n < 0 = strstr "-" . byDigitsOf k (negate n)
            | otherwise = if n >= (10 ^ k) then byDigitsOf k (n `div` (10 ^ k)) . strstr "" . strcat [ shows ((n `div` (10 ^ i)) `mod` 10) | i <- [k - 1, k - 2 .. 0] ] else shows n

instance Outputable Int where
    pprint _ = shows

instance Outputable Unique where
    pprint _ (Unique i) = strstr "#" . shows i

instance Functor m => Functor (UniqueT m) where
    fmap a2b = UniqueT . fmap a2b . runUniqueT

instance Monad m => Applicative (UniqueT m) where
    pure = UniqueT . pure
    (<*>) = ap

instance Monad m => Monad (UniqueT m) where
    m >>= k = UniqueT $ runUniqueT m >>= runUniqueT . k

instance Monad m => MonadUnique (UniqueT m) where
    getUnique = UniqueT $ do
        i <- get
        i `seq` put (succ i)
        return (Unique i)

instance MonadIO m => MonadIO (UniqueT m) where
    liftIO = UniqueT . liftIO

instance MonadTrans UniqueT where
    lift = UniqueT . lift

instance MonadUnique m => MonadUnique (ExceptT e m) where
    getUnique = lift getUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    getUnique = lift getUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    getUnique = lift getUnique

instance IsInt Int where
    toInt = id
    fromInt = id

instance (Outputable key, Outputable val) => Outputable (Map.Map key val) where
    pprint _ m = strstr "Map.fromAscList" . plist 4 [ strstr "(" . pprint 0 k . strstr ", " . pprint 0 v . strstr ")" | (k, v) <- Map.toAscList m ]

instance Show Unique where
    showsPrec _ = shows . unUnique
