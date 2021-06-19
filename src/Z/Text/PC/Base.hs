module Z.Text.PC.Base where

import Control.Applicative
import Data.Function

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
    empty = PAct $ \str -> []
    p1 <|> p2 = PAct $ \str -> [(p1, str), (p2, str)]

returnPB :: val -> PB chr val
returnPB val1 = PVal val1

bindPB :: PB chr val -> (val -> PB chr val') -> PB chr val'
bindPB (PVal val1) p2 = p2 val1
bindPB (PAct act1) p2 = PAct $ \str0 -> [ (bindPB p1 p2, str1) | (p1, str1) <- act1 str0 ]

mkPB :: ([chr] -> [(val, [chr])]) -> PB chr val
mkPB givenReadS = PAct $ \str0 -> [ (PVal val1, str1) | (val1, str1) <- givenReadS str0 ]

runPB :: PB chr val -> [chr] -> [(val, [chr])]
runPB (PVal val1) str = curry return val1 str
runPB (PAct act1) str = act1 str >>= uncurry runPB
