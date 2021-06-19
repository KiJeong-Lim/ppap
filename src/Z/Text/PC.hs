module Z.Text.PC where

import Control.Applicative
import Data.Function
import Z.Algo.Sorting
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

type PC = MyPC

type ErrorMessage = String

autoPC :: Read val => PC val
autoPC = MyPC go where
    go :: Read val => PB LocChr val
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
    go :: String -> PB LocChr ()
    go expecteds = mkPB $ \lstr0 -> case splitAt (length expecteds) lstr0 of
        (token, lstr1) -> if map snd token == expecteds then [((), lstr1)] else []

eofPC :: PC ()
eofPC = MyPC go where
    go :: PB LocChr ()
    go = mkPB $ \lstr0 -> if null lstr0 then [((), lstr0)] else []

regexPC :: RegExRep -> PC String
regexPC = myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression

negPC :: PC val -> PC ()
negPC = MyPC . go . unMyPC where
    go :: PB LocChr val -> ParserBase LocChr ()
    go p1 = mkPB $ \str0 -> if null (runPB p1 str0) then [((), str0)] else []

execPC :: PC val -> Src -> Either LocStr val
execPC = go where
    findShortest :: [[chr]] -> [chr]
    findShortest = head . sortByMerging ((<=) `on` length)
    execPB :: PB chr val -> [chr] -> Either [chr] [(val, [chr])]
    execPB (PVal val1) lstr0 = return [(val1, lstr0)]
    execPB (PAct act1) lstr0 = case [ execPB p1 lstr1 | (p1, lstr1) <- act1 lstr0 ] of
        [] -> callWithStrictArg Left lstr0
        results -> case [ (val2, lstr2) | Right pairs <- results, (val2, lstr2) <- pairs ] of
            [] -> callWithStrictArg Left (findShortest [ lstr2 | Left lstr2 <- results ])
            pairs -> return pairs
    go :: PC val -> Src -> Either LocStr val
    go p str0 = case execPB (unMyPC p) (addLoc str0) of
        Left lstr -> callWithStrictArg Left lstr
        Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
            [] -> callWithStrictArg Left (findShortest (map snd pairs))
            val : _ -> return val

runPC :: FPath -> PC val -> Src -> Either ErrorMessage val
runPC (FPath { getFilePath = path }) p src = either (callWithStrictArg Left . makeMessageForParsingError path src) (callWithStrictArg return) (execPC p src)

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'])* \"\\\"\""

skipWhite :: PC Int
skipWhite = MyPC go where
    go :: PB LocChr Int
    go = mkPB $ \lstr0 -> case span (\lch -> snd lch == ' ') lstr0 of
        (ws, lstr1) -> [(length ws, lstr1)]

indent :: Indentation -> PC ()
indent = consumePC . flip replicate ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> PC val -> PC [val]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []
