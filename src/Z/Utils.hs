module Z.Utils where

import System.IO

infixl 1 <<

type Precedence = Int

newtype FPath
    = FPath { getFilePath :: FilePath }
    deriving ()

class OStreamMaker seed where
    mkOStream :: seed -> IO Handle

class OStreamObject a where
    intoString :: a -> String

instance Show FPath where
    showsPrec _ (FPath path) = showString path

instance OStreamMaker Handle where
    mkOStream = pure

instance OStreamMaker a => OStreamMaker (IO a) where
    mkOStream m = m >>= mkOStream

instance OStreamMaker FPath where
    mkOStream (FPath path) = openFile path WriteMode

instance OStreamObject Char where
    intoString ch = return ch

instance OStreamObject a => OStreamObject [a] where
    intoString xs = xs >>= intoString

instance OStreamObject Int where
    intoString i = shows i ""

instance OStreamObject Double where
    intoString x = shows x ""

instance OStreamObject Integer where
    intoString n = shows n ""

cout :: Handle
cout = stdout

cerr :: Handle
cerr = stderr

endl :: Char
endl = '\n'

(<<) :: (OStreamMaker seed, OStreamObject a) => seed -> a -> IO Handle
seed << x = do
    h <- mkOStream seed
    hPutStr h (intoString x)
    hFlush h
    return h

int :: Integral a => a -> Int
int = fromInteger . toInteger

double :: Double -> Double
double = id

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

mkFPath :: FilePath -> FPath
mkFPath = callWithStrictArg FPath . map (\ch -> if ch == '\\' then '/' else ch)
