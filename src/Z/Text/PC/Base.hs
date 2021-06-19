module Z.Text.PC.Base where

import Control.Applicative
import Control.Monad
import Data.Function

data ParserBase chr val
    = PVal val
    | PAlt [(ParserBase chr val, [chr])]
    | PAct ([chr] -> ParserBase chr val)
    deriving ()

instance Functor (ParserBase chr) where
    fmap a2b = flip bindPB (returnPB . a2b)

instance Applicative (ParserBase chr) where
    pure = returnPB
    p1 <*> p2 = bindPB p1 (flip fmap p2)

instance Monad (ParserBase chr) where
    p1 >>= p2 = bindPB p1 p2

instance Alternative (ParserBase chr) where
    empty = PAlt []
    p1 <|> p2 = PAct $ \str -> PAlt [(p1, str), (p2, str)]

instance MonadPlus (ParserBase chr) where

instance Semigroup (ParserBase chr val) where
    (<>) = (<|>)

instance Monoid (ParserBase chr val) where
    mempty = empty

returnPB :: val -> ParserBase chr val
returnPB = PVal

bindPB :: ParserBase chr val1 -> (val1 -> ParserBase chr val2) -> ParserBase chr val2
bindPB (PVal val1) p2 = p2 val1
bindPB (PAlt alts1) p2 = PAlt [ (bindPB p1 p2, str1) | (p1, str1) <- alts1 ]
bindPB (PAct act1) p2 = PAct $ \str0 -> bindPB (act1 str0) p2

mkPB :: ([chr] -> [(val, [chr])]) -> ParserBase chr val
mkPB _ReadS = PAct $ \str0 -> PAlt [ (PVal val1, str1) | (val1, str1) <- _ReadS str0 ]

runPB :: ParserBase chr val -> [chr] -> [(val, [chr])]
runPB (PVal val) str = return (val, str)
runPB (PAlt alts) str = alts >>= uncurry runPB
runPB (PAct act) str = runPB (act str) str
