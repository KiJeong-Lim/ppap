module Z.Text.PC where

import Control.Applicative
import Data.Function
import Z.Algo.Sorting
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

type PC = MyPC

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
    go :: PB LocChr val -> PB LocChr ()
    go p1 = mkPB $ \str0 -> if null (runPB p1 str0) then [((), str0)] else []

execPC :: PC val -> Src -> Either LocStr val
execPC p str = execPB (unMyPC p) (addLoc str)

runPC :: FPath -> PC val -> Src -> Either ErrMsg val
runPC (FPath { getFilePath = path }) p src = either (callWithStrictArg Left . makeMessageForParsingError path src) (callWithStrictArg return) (execPC p src)

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'])* \"\\\"\""

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
