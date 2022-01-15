module Z.Text.PC.Base where

import Control.Applicative
import Control.Monad
import Data.Function
import Z.Algo.Sorting

type PB = ParserBase

data ParserBase chr val
    = PVal val
    | PAct ([chr] -> [(ParserBase chr val, [chr])])
    deriving ()

instance Functor (ParserBase chr) where
    fmap a2b = flip bindPB (returnPB . a2b)

instance Applicative (ParserBase chr) where
    pure = returnPB
    p1 <*> p2 = bindPB p1 (flip fmap p2)

instance Monad (ParserBase chr) where
    p1 >>= p2 = bindPB p1 p2

instance Alternative (ParserBase chr) where
    empty = emptyPB
    p1 <|> p2 = appendPB p1 p2

instance MonadPlus (ParserBase chr) where

returnPB :: val -> PB chr val
returnPB val1 = PVal val1

bindPB :: PB chr val -> (val -> PB chr val') -> PB chr val'
bindPB (PVal val1) p2 = p2 val1
bindPB (PAct act1) p2 = PAct $ \str0 -> [ (bindPB p1 p2, str1) | (p1, str1) <- act1 str0 ]

emptyPB :: PB chr val
emptyPB = PAct $ \str0 -> []

appendPB :: PB chr val -> PB chr val -> PB chr val
appendPB p1 p2 = PAct $ \str0 -> [(p1, str0), (p2, str0)]

mkPB :: ([chr] -> [(val, [chr])]) -> PB chr val
mkPB givenReadS = PAct $ \str0 -> [ (PVal val1, str1) | (val1, str1) <- givenReadS str0 ]

runPB :: PB chr val -> [chr] -> [(val, [chr])]
runPB (PVal val1) = curry return val1
runPB (PAct act1) = uncurry runPB <=< act1

execPB :: PB chr val -> [chr] -> Either [chr] val
execPB = go where
    strictLeft :: a -> Either a b
    strictLeft x = x `seq` Left x
    findShortest :: [[chr]] -> [chr]
    findShortest = head . sortByMerging ((<=) `on` length)
    loop :: PB chr val -> [chr] -> Either [chr] [(val, [chr])]
    loop (PVal val1) lstr0 = return [(val1, lstr0)]
    loop (PAct act1) lstr0 = case [ loop p1 lstr1 | (p1, lstr1) <- act1 lstr0 ] of
        [] -> strictLeft lstr0
        results -> case [ (val2, lstr2) | Right pairs <- results, (val2, lstr2) <- pairs ] of
            [] -> strictLeft (findShortest [ lstr2 | Left lstr2 <- results ])
            pairs -> return pairs
    go :: PB chr val -> [chr] -> Either [chr] val
    go p lstr0 = case loop p lstr0 of
        Left lstr1 -> strictLeft lstr1
        Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
            [] -> strictLeft (findShortest (map snd pairs))
            val : _ -> return val
