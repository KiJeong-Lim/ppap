module Z.Text.PC where

import Control.Applicative
import Data.Function
import Z.Algo.Sorting
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

type PC = P

autoPC :: Read val => PC val
autoPC = PC go where
    go :: Read val => ParserBase LocChr val
    go = PAct $ \lstr0 -> PAlt [ (PVal val1, drop (length lstr0 - length str1) lstr0) | (val1, str1) <- readsPrec 0 (map snd lstr0) ]

acceptPC :: (Char -> Bool) -> PC Char
acceptPC cond = PC go where
    go :: ParserBase LocChr Char
    go = PAct $ \lstr -> case lstr of
        ((r, c), ch) : lstr'
            | cond ch -> PAlt [(PVal ch, lstr')]
        _ -> PAlt []

consumePC :: String -> PC ()
consumePC = mapM_ acceptPC . map (==)

matchPC :: String -> PC ()
matchPC = PC . go where
    go :: String -> ParserBase LocChr ()
    go expecteds = PAct $ \lstr0 -> if expecteds == map snd (take (length expecteds) lstr0) then PAlt [(PVal (), drop (length expecteds) lstr0)] else PAlt []

eofPC :: PC ()
eofPC = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> if null lstr0 then PAlt [(PVal (), lstr0)] else PAlt []

regexPC :: RegExRep -> PC String
regexPC = parserByRegularExpression

negPC :: PC a -> PC ()
negPC = PC . negPB . unPC

runPC :: PC val -> Src -> Either String val
runPC p str0
    = case runPB (unPC p) (addLoc str0) of
        Left lstr -> callWithStrictArg Left (mkErrMsg str0 lstr)
        Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
            [] -> callWithStrictArg Left (mkErrMsg str0 (head (sortByMerging ((<=) `on` length) (map snd pairs))))
            val : _ -> return val

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'])* \"\\\"\""

skipWhite :: PC Int
skipWhite = PC go where
    go :: ParserBase LocChr Int
    go = PAct $ \lstr0 -> case span (\lch -> snd lch == ' ') lstr0 of
        (ws, lstr1) -> PAlt [(PVal (length ws), lstr1)]

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> PC ()
indent = consumePC . flip replicate ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> PC a -> PC [a]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []
