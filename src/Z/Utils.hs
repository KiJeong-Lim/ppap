module Z.Utils where

import Control.Monad
import Data.Function
import Data.List
import System.IO

infixl 1 <<

type Precedence = Int

class OStreamMaker seed where
    mkOStream :: seed -> IO Handle

class OStreamObject a where
    hput :: Handle -> a -> IO ()

instance OStreamMaker Handle where
    mkOStream = return

instance OStreamMaker a => OStreamMaker (IO a) where
    mkOStream = id >=> mkOStream

instance OStreamObject Char where
    hput = hPutChar

instance OStreamObject a => OStreamObject [a] where
    hput = mapM_ . hput

instance OStreamObject Int where
    hput h = hPutShowS h . shows

instance OStreamObject Double where
    hput h = hPutShowS h . shows

instance OStreamObject Integer where
    hput h = hPutShowS h . shows

instance OStreamObject Bool where
    hput h b = hPutStr h (if b then "true" else "false")

hPutShowS :: Handle -> ShowS -> IO ()
hPutShowS my_handle = hPutStr my_handle . initShowS

initShowS :: ShowS -> String
initShowS string_stream = string_stream ""

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
splitBy x0 = fix $ \my_fix -> callWithStrictArg (uncurry $ \xs -> if null xs then maybe [] (mappend (one xs) . my_fix . snd) . uncons else mappend (one xs) . my_fix) . span (\x -> x /= x0)

calcTab :: Int -> Int
calcTab n = myTabSize - (n `mod` myTabSize) where
    myTabSize :: Int
    myTabSize = 4

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg = ($!)

one :: a -> [a]
one = callWithStrictArg pure

modifySep :: Eq a => a -> (a -> [b]) -> ([a] -> [b]) -> ([a] -> [b])
modifySep x0 f g = callWithStrictArg (\zs -> concat . foldr (\ys -> \acc -> if null acc then ys : acc else ys : zs : acc) [] . map g . splitBy x0) (f x0)

findAllPermutationsOf :: [a] -> [[a]]
findAllPermutationsOf xs = swag [0 .. length xs - 1] (\k -> xs !! k) where
    swag :: [Int] -> ((Int -> a) -> [[a]])
    swag my_range = foldr (\n -> \kont -> \at -> [0 .. n] >>= kont . curry (applySwapping at) n) (\at -> return (map at my_range)) my_range
    applySwapping :: (Int -> a) -> (Int, Int) -> (Int -> a)
    applySwapping at (i, j) = maybe . at <*> flip pure <*> flip lookup [(i, at j), (j, at i)]
