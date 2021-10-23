module Z.Utils where

import Data.List
import System.IO

infixl 1 <<

type Precedence = Int

class OStreamMaker seed where
    mkOStream :: seed -> IO Handle

class OStreamObject a where
    hput :: Handle -> a -> IO ()

instance OStreamMaker Handle where
    mkOStream = pure

instance OStreamMaker a => OStreamMaker (IO a) where
    mkOStream m = m >>= mkOStream

instance OStreamObject Char where
    hput = hPutChar

instance OStreamObject a => OStreamObject [a] where
    hput = mapM_ . hput

instance OStreamObject Int where
    hput h = hPutStr h . show

instance OStreamObject Double where
    hput h = hPutStr h . show

instance OStreamObject Integer where
    hput h = hPutStr h . show

instance OStreamObject Bool where
    hput h b = hput h (if b then "true" else "false")

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
    hFlush h
    return h

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless cond = foldr (\x -> maybe [one x] (uncurry $ \xs -> mappend (if cond x (head xs) then [one x ++ xs] else [one x] ++ [xs])) . uncons) []

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x0 = (uncurry $ \xs -> if null xs then maybe [] (mappend (one xs) . splitBy x0 . snd) . uncons else mappend (one xs) . splitBy x0) . span (\x -> x /= x0)

calcTab :: Int -> Int
calcTab n = myTabSize - (n `mod` myTabSize) where
    myTabSize :: Int
    myTabSize = 4

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg = ($!)

one :: a -> [a]
one = callWithStrictArg pure

modifySep :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySep x f g = concat . foldr (\ys -> \acc -> if null acc then ys : acc else ys : f x : acc) [] . map g . splitBy x

findAllPermutationsOf :: [a] -> [[a]]
findAllPermutationsOf xs = swag (\at -> uncurry $ \i -> \j -> maybe . at <*> flip pure <*> flip lookup [(i, at j), (j, at i)]) [0 .. length xs - 1] (\k -> xs !! k) where
    swag :: ((Int -> a) -> (Int, Int) -> (Int -> a)) -> [Int] -> ((Int -> a) -> [[a]])
    swag my_swap my_range = foldr (\n -> \kont -> \at -> [0 .. n] >>= kont . curry (my_swap at) n) (\at -> return (map at my_range)) my_range
