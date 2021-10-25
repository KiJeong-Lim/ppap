module Z.Utils where

import Control.Monad
import Data.Function
import Data.List
import System.IO

infixl 1 <<

type Precedence = Int

data Flush
    = Flush
    deriving (Eq, Ord, Show)

class OStreamTrain os where
    getHandleFrom :: os -> IO Handle

class OStreamCargo a where
    hput :: Handle -> a -> IO ()

instance OStreamTrain (Handle) where
    getHandleFrom = return

instance OStreamTrain a => OStreamTrain (IO a) where
    getHandleFrom = id >=> getHandleFrom

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

instance OStreamCargo (Double) where
    hput h = hput h . shows

instance OStreamCargo (Integer) where
    hput h = hput h . shows

instance OStreamCargo (Bool) where
    hput h b = hput h (if b then "true" else "false")

withZero :: Monoid a => (a -> b) -> b
withZero to_be_initialized = to_be_initialized mempty

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

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless is_related_to = foldr (\x -> maybe [one x] (uncurry $ \xs -> mappend (if x `is_related_to` head xs then [one x ++ xs] else [one x] ++ [xs])) . uncons) []

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x0 = fix $ \my_fix -> callWithStrictArg (uncurry $ \xs -> if null xs then maybe [] (mappend (one xs) . my_fix . snd) . uncons else mappend (one xs) . my_fix) . span (\x -> x /= x0)

calcTab :: Int -> Int
calcTab n = callWithStrictArg (\my_tab_width -> my_tab_width - (n `mod` my_tab_width)) 4

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg = ($!)

one :: a -> [a]
one = callWithStrictArg pure

modifySep :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySep x0 f g = callWithStrictArg (\zs -> concat . foldr (\ys -> \acc -> if null acc then ys : acc else ys : zs : acc) [] . map g . splitBy x0) (f x0)

findAllPermutationsOf :: [a] -> [[a]]
findAllPermutationsOf xs = swag (\at -> uncurry $ \i -> \j -> maybe . at <*> flip pure <*> flip lookup [(i, at j), (j, at i)]) [0 .. length xs - 1] (\k -> xs !! k) where
    swag :: ((Int -> a) -> (Int, Int) -> (Int -> a)) -> [Int] -> ((Int -> a) -> [[a]])
    swag applySwapping my_range = foldr (\n -> \kont -> \at -> [0 .. n] >>= kont . curry (applySwapping at) n) (\at -> return (map at my_range)) my_range

recList :: (r) -> (a -> [a] -> r -> r) -> ([a] -> r)
recList for_nil for_cons = snd . foldr (\my_hd -> uncurry $ \my_tl -> \my_result -> (my_hd : my_tl, for_cons my_hd my_tl my_result)) ([], for_nil)

findLast :: Integral int => (int, int) -> (int -> Bool) -> Maybe int
findLast = uncurry $ \left_bound -> \right_bound -> swag (if left_bound < right_bound then succ else pred) (\n -> n == right_bound) left_bound where
    swag :: (a -> a) -> (a -> Bool) -> a -> (a -> Bool) -> Maybe a
    swag get_the_next_of is_the_last the_first has_wanted_property = fix (\bounded_search -> \n -> (if is_the_last n then id else bounded_search (get_the_next_of n)) . (if has_wanted_property n then const (pure n) else id)) the_first (fail "")
