module Z.Text.PC where

import Control.Applicative
import Control.Monad
import Data.Function
import Z.Algo.Sorting
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

type PC = MyPC

autoPC :: Read val => PC val
autoPC = MyPC go where
    go :: Read val => ParserBase LocChr val
    go = mkPB $ \lstr0 -> [ (val1, drop (length lstr0 - length str1) lstr0) | (val1, str1) <- readsPrec 0 (map snd lstr0) ]

acceptPC :: (Char -> Bool) -> PC Char
acceptPC = MyPC . go where
    go :: (Char -> Bool) -> ParserBase LocChr Char
    go cond = mkPB $ \lstr -> case lstr of
        [] -> []
        ((r, c), ch) : lstr' -> if cond ch then [(ch, lstr')] else []

consumePC :: String -> PC ()
consumePC = mapM_ acceptPC . map (==)

matchPC :: String -> PC ()
matchPC = MyPC . go where
    go :: String -> ParserBase LocChr ()
    go expecteds = mkPB $ \lstr0 -> case splitAt (length expecteds) lstr0 of
        (token, lstr1) -> if map snd token == expecteds then [((), lstr1)] else []

eofPC :: PC ()
eofPC = MyPC go where
    go :: ParserBase LocChr ()
    go = mkPB $ \lstr0 -> if null lstr0 then [((), lstr0)] else []

regexPC :: RegExRep -> PC String
regexPC = myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression

negPC :: PC val -> PC ()
negPC = MyPC . go . unMyPC where
    go :: ParserBase LocChr val -> ParserBase LocChr ()
    go p1 = mkPB $ \str0 -> if null (runPB p1 str0) then [((), str0)] else []

execPC :: FPath -> PC val -> Src -> Either String val
execPC (FPath { getFilePath = path }) = go where
    findShortest :: [[chr]] -> [chr]
    findShortest = head . sortByMerging ((<=) `on` length)
    execPB :: ParserBase chr val -> [chr] -> Either [chr] [(val, [chr])]
    execPB (PVal val1) lstr0 = return [(val1, lstr0)]
    execPB (PAlt alts1) lstr0 = case [ execPB p1 lstr1 | (p1, lstr1) <- alts1 ] of
        [] -> Left lstr0
        results -> case [ (val2, lstr2) | Right pairs <- results, (val2, lstr2) <- pairs ] of
            [] -> callWithStrictArg Left (findShortest [ lstr2 | Left lstr2 <- results ])
            pairs -> return pairs
    execPB (PAct act1) lstr0 = execPB (act1 lstr0) lstr0
    go :: PC val -> Src -> Either String val
    go p str0 = case execPB (unMyPC p) (addLoc str0) of
        Left lstr -> callWithStrictArg Left (makeMessageForParsingError path str0 lstr)
        Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
            [] -> callWithStrictArg Left (makeMessageForParsingError path str0 (findShortest (map snd pairs)))
            val : _ -> return val

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'])* \"\\\"\""

skipWhite :: PC Int
skipWhite = MyPC go where
    go :: ParserBase LocChr Int
    go = mkPB $ \lstr0 -> case span (\lch -> snd lch == ' ') lstr0 of
        (ws, lstr1) -> [(length ws, lstr1)]

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Indentation -> PC ()
indent = consumePC . flip replicate ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> PC val -> PC [val]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []
