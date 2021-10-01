module Z.Utils where

import System.IO

infixl 1 <<

type Precedence = Int

data Flush
    = Flush
    deriving ()

class OStreamMaker seed where
    mkOStream :: seed -> IO Handle

class OStreamObject a where
    hput :: Handle -> a -> IO ()

instance OStreamMaker Handle where
    mkOStream = pure

instance OStreamMaker a => OStreamMaker (IO a) where
    mkOStream m = m >>= mkOStream

instance OStreamObject Flush where
    hput h _ = hFlush h

instance OStreamObject Char where
    hput h ch = hPutChar h ch

instance OStreamObject a => OStreamObject [a] where
    hput h = mapM_ (hput h)

instance OStreamObject Int where
    hput h = hput h . show

instance OStreamObject Double where
    hput h = hput h . show

instance OStreamObject Integer where
    hput h = hput h . show

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
    return h

splitUnless :: (a -> a -> Bool) -> [a] -> [[a]]
splitUnless cond (x1 : x2 : xs)
    | cond x1 x2 = case splitUnless cond (x2 : xs) of
        y : ys -> (x1 : y) : ys
splitUnless cond [] = []
splitUnless cond (x1 : xs) = [x1] : splitUnless cond xs

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x0 [] = [[]]
splitBy x0 (x : xs)
    | x == x0 = [] : splitBy x0 xs
    | otherwise = case splitBy x0 xs of
        y : ys -> (x : y) : ys

calcTab :: Int -> Int
calcTab n = myTabSize - (n `mod` myTabSize) where
    myTabSize :: Int
    myTabSize = 4

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg f x = x `seq` f x

one :: a -> [a]
one = callWithStrictArg pure
