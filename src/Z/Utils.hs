module Z.Utils where

import Control.Monad
import Data.Function
import Data.List
import System.IO

infixl 1 <<

type Precedence = Int

data Flush
    = Flush
    deriving (Eq, Show)

class OStreamMaker seed where
    mkOStream :: seed -> IO Handle

class OStreamObject a where
    hput :: Handle -> a -> IO ()

instance OStreamMaker (Handle) where
    mkOStream = return

instance OStreamMaker a => OStreamMaker (IO a) where
    mkOStream = id >=> mkOStream

instance OStreamObject (Char) where
    hput = hPutChar

instance OStreamObject a => OStreamObject [a] where
    hput = mapM_ . hput

instance (Monoid a, OStreamObject b) => OStreamObject (a -> b) where
    hput h = hput h . withZero

instance OStreamObject (Flush) where
    hput = const . hFlush

instance OStreamObject (Int) where
    hput h = hput h . shows

instance OStreamObject (Double) where
    hput h = hput h . shows

instance OStreamObject (Integer) where
    hput h = hput h . shows

instance OStreamObject (Bool) where
    hput h b = hput h (if b then "true" else "false")

withZero :: Monoid a => (a -> b) -> b
withZero = flip callWithStrictArg mempty

cout :: Handle
cout = stdout

cerr :: Handle
cerr = stderr

endl :: Char
endl = '\n'

(<<) :: (OStreamMaker seed, OStreamObject a) => seed -> a -> IO Handle
seed << x = do
    h <- mkOStream seed
    hput h x
    return h

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless cond = foldr (\x -> maybe [one x] (uncurry $ \xs -> mappend (if cond x (head xs) then [one x ++ xs] else [one x] ++ [xs])) . uncons) []

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
