module Z.Text.PC where

import Control.Applicative
import Control.Monad
import Data.Function
import Z.Algo.Sorting
import Z.Text.PC.Base
import Z.Text.PC.Internal

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
consumePC expecteds = mapM_ acceptPC (map (==) expecteds)

matchPC :: String -> PC ()
matchPC expecteds = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> if expecteds == map snd (take (length expecteds) lstr0) then PAlt [(PVal (), drop (length expecteds) lstr0)] else PAlt []

eofPC :: PC ()
eofPC = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> if null lstr0 then PAlt [(PVal (), lstr0)] else PAlt []

regexPC :: RegExRep -> PC String
regexPC = parserByRegularExpression

negPC :: PC a -> PC ()
negPC = PC . negPB . unPC

runPC :: PC val -> Src -> Either String val
runPC p str0 = case runPB (unPC p) (addLoc str0) of
    Left lstr -> Left (mkErrMsg str0 lstr)
    Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
        [] -> Left (mkErrMsg str0 (head (sortByMerging (on (<=) length) (map snd pairs))))
        val : _ -> Right val

acceptQuote :: PC String
acceptQuote = PC go where
    loop :: LocStr -> Either LocStr (String, LocStr)
    loop lstr0 = case map snd (take 1 lstr0) of
        [] -> Left lstr0
        ['\\'] -> case map snd (take 1 (drop 1 lstr0)) of
            ['\"'] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\"' : quote, lstr1)
            ['\''] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\'' : quote, lstr1)
            ['\\']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\\' : quote, lstr1)
            ['\n']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\n' : quote, lstr1)
            ['\t']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\t' : quote, lstr1)
            _ -> Left lstr0
        ['\n'] -> Left lstr0
        ['\t'] -> Left lstr0
        ['\"'] -> return ("", drop 1 lstr0)
        [ch] -> do
                (quote, lstr1) <- loop (drop 1 lstr0)
                return (ch : quote, lstr1)
    go :: ParserBase LocChr String
    go = PAct $ \lstr0 -> case lstr0 of
        (_, '\"') : lstr1 -> case loop lstr1 of
            Left lstr2 -> PAlt []
            Right (quote, lstr2) -> PAlt [(PVal quote, lstr2)]
        lstr1 -> PAlt []

skipWhite :: PC ()
skipWhite = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> PAlt [(PVal (), dropWhile (\lch -> snd lch == ' ') lstr0)]

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> PC ()
indent n = consumePC space where
    space :: String
    space = replicate n ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> PC a -> PC [a]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []
