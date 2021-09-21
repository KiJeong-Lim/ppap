module Z.Text.PC where

import Control.Applicative
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

type PC = MyPC

acceptPC :: (Char -> Bool) -> PC Char
acceptPC cond = MyPC (mkPB go) where
    go :: LocStr -> [(Char, LocStr)]
    go [] = []
    go (((r, c), ch) : lstr') = if cond ch then [(ch, lstr')] else []

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

intPC :: PC Int
intPC = read <$> regexPC "['-']? ['0'-'9']+"

negPC :: PC val -> PC ()
negPC = MyPC . go . unMyPC where
    go :: PB LocChr val -> PB LocChr ()
    go p1 = mkPB $ \str0 -> if null (runPB p1 str0) then [((), str0)] else []

execPC :: PC val -> Src -> Either LocStr val
execPC p str = execPB (unMyPC p) (addLoc str)

runPC :: FPath -> PC val -> Src -> Either ErrMsg val
runPC (FPath { getFilePath = path }) p src = either (callWithStrictArg Left . makeMessageForParsingError path src) (callWithStrictArg return) (execPC p src)

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\\\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'\\\'\\\\\'])* \"\\\"\""

skipWhite :: PC Int
skipWhite = MyPC go where
    go :: PB LocChr Int
    go = mkPB $ \lstr0 -> case span (\lch -> snd lch == ' ') lstr0 of
        (ws, lstr1) -> [(length ws, lstr1)]

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> PC val -> PC [val]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []

parenPC :: Char -> Char -> PC val -> PC val
parenPC ch1 ch2 p = acceptPC (\ch -> ch == ch1) *> p <* acceptPC (\ch -> ch == ch2)

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> PC ()
indent n = consumePC (replicate n ' ')

charPC :: PC Char
charPC = pure read <*> regexPC "\"\\\'\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\\\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'\\\'\\\\\']) \"\\\'\""

acceptList :: PC a -> PC [a]
acceptList pc = consumePC "[" *> (skipWhite *> (pure [] <|> (pure (:) <*> pc <*> many (consumePC "," *> skipWhite *> pc)))) <* consumePC "]"
