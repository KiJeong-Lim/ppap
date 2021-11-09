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

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless is_related_to = foldr (\x -> recList [pure x] (\xs -> if x `is_related_to` head xs then const . kons (pure x ++ xs) else const . kons (pure x) . kons xs)) []

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x0 = fix (\swag -> flip (recList (\buffer -> [reverse buffer]) (\x -> \xs -> \go -> \buffer -> if x == x0 then [reverse buffer] ++ swag xs else go (x : buffer))) [])

calcTab :: Int -> Int
calcTab n = 4 & (\my_tab_width -> my_tab_width - n `mod` my_tab_width)

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg f x = f $! x

one :: a -> [a]
one = callWithStrictArg pure

modifySep :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySep x0 f1 f2 = f1 x0 & (\zs -> concat . foldr (\ys -> \acc -> if null acc then ys : acc else ys : zs : acc) [] . map f2 . splitBy x0)

findAllPermutationsOf :: [a] -> [[a]]
findAllPermutationsOf = swag (\at -> uncurry $ \i -> \j -> maybe . at <*> curry snd <*> flip lookup [(i, at j), (j, at i)]) . zipWith const [0 ..] <*> (!!) where
    swag :: ((Int -> a) -> (Int, Int) -> (Int -> a)) -> [Int] -> ((Int -> a) -> [[a]])
    swag my_swap all_idxes = foldr (\n -> \kont -> \at -> [0 .. n] >>= kont . curry (my_swap at) n) (\at -> return (map at all_idxes)) all_idxes

recList :: (r) -> (a -> [a] -> r -> r) -> ([a] -> r)
recList for_nil for_cons = snd . foldr (\my_hd -> uncurry $ \my_tl -> \my_result -> (my_hd : my_tl, for_cons my_hd my_tl my_result)) ([], for_nil)

findLast :: Integral int => (int, int) -> (int -> Bool) -> Maybe int
findLast = uncurry $ \left_bound -> \right_bound -> swag (if left_bound < right_bound then succ else pred) (\n -> right_bound == n) left_bound where
    swag :: (a -> a) -> (a -> Bool) -> a -> (a -> Bool) -> Maybe a
    swag get_the_next_of is_the_last the_first has_wanted_property = fix (\bounded_search -> \n -> (if is_the_last n then id else bounded_search (get_the_next_of n)) . (if has_wanted_property n then const (pure n) else id)) the_first (fail "")
