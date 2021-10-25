module Z.Text.PC.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import Z.Algo.Function
import Z.Algo.Sorting
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PM
import Z.Utils

type Row = Int

type Col = Int

type LocChr = ((Row, Col), Char)

type LocStr = [LocChr]

type Src = String

type ErrMsg = String

type RegExRep = String

type DoesMyCharSetAcceptSomeChar = CharSet -> Bool

type IsItPossibleThatMyRegexAcceptNonemptyString = RegEx -> Bool

data CharSet
    = CsUniv
    | CsPlus CharSet CharSet
    | CsDiff CharSet CharSet
    | CsEnum Char Char
    | CsUnit Char
    deriving ()

data RegEx
    = ReCSet CharSet
    | ReWord String
    | RePlus RegEx RegEx
    | ReZero
    | ReMult RegEx RegEx
    | ReStar RegEx
    deriving ()

newtype MyPC val
    = MyPC { unMyPC :: ParserBase LocChr val }
    deriving ()

instance Functor MyPC where
    fmap a2b = MyPC . fmap a2b . unMyPC

instance Applicative MyPC where
    pure = MyPC . pure
    p1 <*> p2 = MyPC (unMyPC p1 <*> unMyPC p2)

instance Monad MyPC where
    p1 >>= p2 = MyPC (unMyPC p1 >>= unMyPC . p2)

instance Alternative MyPC where
    empty = MyPC empty
    p1 <|> p2 = MyPC (unMyPC p1 <|> unMyPC p2)

instance MonadPlus MyPC where

instance MonadFail MyPC where
    fail = const empty

instance Semigroup (MyPC val) where
    p1 <> p2 = p1 <|> p2

instance Monoid (MyPC val) where
    mempty = empty

instance Read CharSet where
    readsPrec = unPM . go where
        go :: Precedence -> PM CharSet
        go 0 = List.foldl' mkCsDiff <$> go 1 <*> many (consumeStr "\\" *> go 2)
        go 1 = List.foldl' mkCsPlus <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = mconcat
            [ mkCsUnit <$> autoPM 0
            , mkCsEnum <$> autoPM 0 <* consumeStr "-" <*> autoPM 0
            , consumeStr "." *> pure mkCsUniv
            , go 3
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

instance Show CharSet where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then showChar '(' . ss . showChar ')' else ss
        dispatch :: CharSet -> ShowS
        dispatch (CsDiff chs1 chs2) = myPrecIs 0 (showsPrec 0 chs1 . showString "\\" . showsPrec 2 chs2)
        dispatch (CsPlus chs1 chs2) = myPrecIs 1 (showsPrec 1 chs1 . showString " " . showsPrec 2 chs2)
        dispatch (CsUnit ch) = myPrecIs 2 (shows ch)
        dispatch (CsEnum ch1 ch2) = myPrecIs 2 (shows ch1 . showString "-" . shows ch2)
        dispatch (CsUniv) = myPrecIs 2 (showString ".")
    showList = undefined

instance Read RegEx where
    readsPrec = unPM . go where
        suffix :: PM (RegEx -> RegEx)
        suffix = mconcat
            [ consumeStr "*" *> pure (\re -> mkReStar re)
            , consumeStr "+" *> pure (\re -> mkReMult re (mkReStar re))
            , consumeStr "?" *> pure (\re -> mkRePlus re (mkReWord ""))
            ]
        go :: Precedence -> PM RegEx
        go 0 = List.foldl' mkRePlus <$> go 1 <*> many (consumeStr " + " *> go 1)
        go 1 = List.foldl' mkReMult <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = List.foldl' (flip ($)) <$> go 3 <*> many suffix
        go 3 = mconcat
            [ consumeStr "[" *> (mkReCSet <$> autoPM 0) <* consumeStr "]"
            , pure mkReWord <* matchPrefix "\"" <*> autoPM 0
            , consumeStr "()" *> pure mkReZero
            , go 4
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

instance Show RegEx where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then showChar '(' . ss . showChar ')' else ss
        dispatch :: RegEx -> ShowS
        dispatch (ReCSet chs) = myPrecIs 3 (showString "[" . shows chs . showString "]")
        dispatch (ReWord str) = myPrecIs 3 (shows str)
        dispatch (RePlus re1 re2) = myPrecIs 0 (showsPrec 0 re1 . showString " + " . showsPrec 1 re2)
        dispatch (ReZero) = myPrecIs 3 (showString "()")
        dispatch (ReMult re1 re2) = myPrecIs 1 (showsPrec 1 re1 . showString " " . showsPrec 2 re2)
        dispatch (ReStar re1) = myPrecIs 2 (showsPrec 2 re1 . showString "*")
    showList = undefined

instance Failable (MyPC val) where
    alt = liftBinaryOp $ mkPB . uncurry alt . (runPB <^> runPB)

instance FailableZero (MyPC val) where
    nil = liftNullaryOp $ mkPB . const nil . id

liftBinaryOp :: ((PB LocChr val, PB LocChr val) -> PB LocChr val) -> (MyPC val -> MyPC val -> MyPC val)
liftBinaryOp my_op = curry $ MyPC . my_op . (unMyPC <^> unMyPC)

liftNullaryOp :: (() -> PB LocChr val) -> MyPC val
liftNullaryOp my_op = withZero $ MyPC . my_op . id

initRow :: Row
initRow = 1

initCol :: Col
initCol = 1

addLoc :: Src -> LocStr
addLoc = flip (foldr (\ch -> \kont -> uncurry $ \r -> \c -> ((r, c), ch) : kont (getNextRow r ch, getNextCol c ch)) (const [])) (initRow, initCol) where
    getNextRow :: Row -> Char -> Row
    getNextRow r '\n' = succ r
    getNextRow r _ = r
    getNextCol :: Col -> Char -> Col
    getNextCol c '\n' = initCol
    getNextCol c '\t' = c + calcTab (c - initCol)
    getNextCol c _ = succ c

makeMessageForParsingError :: FilePath -> Src -> LocStr -> ErrMsg
makeMessageForParsingError path src lstr = show theMsgDoc where
    stuckRow :: Row
    stuckRow = case lstr of
        [] -> length (filter (\lch -> snd lch == '\n') lstr) + initRow
        ((r, c), _) : _ -> r
    stuckLine :: Src
    stuckLine = splitBy '\n' src !! (stuckRow - initRow)
    stuckCol :: Col
    stuckCol = case lstr of
        [] -> length stuckLine + initCol
        ((r, c), _) : _ -> c
    theMsgDoc :: Doc
    theMsgDoc = vcat
        [ pstr path +> pstr ":" +> pp stuckRow +> pstr ":" +> pp stuckCol +> pstr ": error:"
        , pstr "parse error " +> (if null lstr then pstr "at EOF" else pstr "on input `" +> pstr (one (snd (head lstr))) +> pstr "'")
        , pcat
            [ vcat
                [ pstr ""
                , pcat
                    [ pstr " "
                    , pp stuckRow
                    , pstr " "
                    ]
                , pstr ""
                ]
            , beam '|'
            , vcat
                [ pstr " "
                , pstr " " +> pstr stuckLine
                , pstr " " +> pstr (replicate (stuckCol - initCol) ' ') +> pstr "^"
                ]
            ]
        ]

mkCsUniv :: CharSet
mkCsUniv = CsUniv

mkCsPlus :: CharSet -> CharSet -> CharSet
mkCsPlus chs1 chs2 = chs1 `seq` chs2 `seq` CsPlus chs1 chs2

mkCsDiff :: CharSet -> CharSet -> CharSet
mkCsDiff chs1 chs2 = chs1 `seq` chs2 `seq` CsDiff chs1 chs2

mkCsEnum :: Char -> Char -> CharSet
mkCsEnum ch1 ch2 = ch1 `seq` ch2 `seq` CsEnum ch1 ch2

mkCsUnit :: Char -> CharSet
mkCsUnit ch = ch `seq` CsUnit ch

mkReCSet :: CharSet -> RegEx
mkReCSet chs = chs `seq` ReCSet chs

mkReWord :: String -> RegEx
mkReWord str = str `seq` ReWord str

mkRePlus :: RegEx -> RegEx -> RegEx
mkRePlus (ReZero) re = re
mkRePlus re (ReZero) = re
mkRePlus re1 re2 = RePlus re1 re2

mkReZero :: RegEx
mkReZero = ReZero

mkReMult :: RegEx -> RegEx -> RegEx
mkReMult (ReZero) re = ReZero
mkReMult re (ReZero) = ReZero
mkReMult re1 re2 = ReMult re1 re2

mkReStar :: RegEx -> RegEx
mkReStar (ReZero) = ReWord ""
mkReStar re = ReStar re

takeStringMatchedWithRegexFromStreamByMaximalMunchRule :: RegEx -> LocStr -> Maybe (String, LocStr)
takeStringMatchedWithRegexFromStreamByMaximalMunchRule = go where
    runCharSet :: CharSet -> (Char -> Bool)
    runCharSet (CsUniv) ch = True
    runCharSet (CsPlus chs1 chs2) ch = runCharSet chs1 ch || runCharSet chs2 ch
    runCharSet (CsDiff ch1 ch2) ch = runCharSet ch1 ch && not (runCharSet ch2 ch)
    runCharSet (CsEnum ch1 ch2) ch = ch1 <= ch && ch <= ch2
    runCharSet (CsUnit ch1) ch = ch == ch1
    isNullable :: RegEx -> Bool
    isNullable (ReCSet chs) = False
    isNullable (ReWord str) = null str
    isNullable (RePlus re1 re2) = isNullable re1 || isNullable re2
    isNullable (ReZero) = False
    isNullable (ReMult re1 re2) = isNullable re1 && isNullable re2
    isNullable (ReStar re1) = True
    differentiate :: Char -> (RegEx -> RegEx)
    differentiate ch (ReCSet chs)
        | runCharSet chs ch = mkReWord ""
        | otherwise = mkReZero
    differentiate ch (ReWord str)
        | [ch] == take 1 str = mkReWord (tail str)
        | otherwise = mkReZero
    differentiate ch (RePlus re1 re2)
        = mkRePlus (differentiate ch re1) (differentiate ch re2)
    differentiate ch (ReZero)
        = mkReZero
    differentiate ch (ReMult re1 re2)
        | isNullable re1 = mkRePlus (differentiate ch re2) (mkReMult (differentiate ch re1) re2)
        | otherwise = mkReMult (differentiate ch re1) re2
    differentiate ch (ReStar re1)
        = mkReMult (differentiate ch re1) (mkReStar re1)
    isNotEmpty :: DoesMyCharSetAcceptSomeChar
    isNotEmpty _ = True
    mayPlvsVltra :: IsItPossibleThatMyRegexAcceptNonemptyString
    mayPlvsVltra (ReCSet chs) = isNotEmpty chs
    mayPlvsVltra (ReWord str) = not (null str)
    mayPlvsVltra (RePlus re1 re2) = or
        [ mayPlvsVltra re1
        , mayPlvsVltra re2
        ]
    mayPlvsVltra (ReZero) = False
    mayPlvsVltra (ReMult re1 re2) = or
        [ mayPlvsVltra re1 && mayPlvsVltra re2
        , mayPlvsVltra re1 && isNullable re2
        , isNullable re1 && mayPlvsVltra re2
        ]
    mayPlvsVltra (ReStar re1) = mayPlvsVltra re1
    repeatPlvsVltra :: String -> RegEx -> StateT LocStr Maybe (String, RegEx)
    repeatPlvsVltra output regex = do
        buffer <- get
        case buffer of
            [] -> if isNullable regex
                then return (output, regex)
                else fail "It is impossible that I read the buffer further more and then accept the given regex."
            ((_, ch) : buffer') -> do
                put buffer'
                let regex' = differentiate ch regex
                    output' = ch : output
                if isNullable regex'
                    then return (output', regex')
                    else if mayPlvsVltra regex'
                        then repeatPlvsVltra output' regex'
                        else fail "It is impossible that I read the buffer further more and then accept the given regex."
    getBuffer :: (LocStr, String) -> LocStr
    getBuffer commit = fst commit
    getOutput :: (LocStr, String) -> String
    getOutput commit = snd commit
    runRegEx :: RegEx -> (LocStr, String) -> (LocStr, String)
    runRegEx current_regex last_commit
        = case runStateT (repeatPlvsVltra "" current_regex) (getBuffer last_commit) of
            Nothing -> last_commit
            Just ((revesed_token_of_output, next_regex), new_buffer)
                | null new_buffer -> commit
                | otherwise -> runRegEx next_regex commit
                where
                    commit :: (LocStr, String)
                    commit = (new_buffer, getOutput last_commit ++ reverse revesed_token_of_output)
    go :: RegEx -> LocStr -> Maybe (String, LocStr)
    go regex lstr0 = case runRegEx regex (lstr0, "") of
        (lstr1, output) -> if not (null output) || isNullable regex then return (output, lstr1) else Nothing

myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression :: RegExRep -> MyPC String
myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression regex_representation = MyPC (go [ regex | (regex, "") <- readsPrec 0 regex_representation ]) where
    myErrMsg :: ErrMsg
    myErrMsg = concat
        [ "In `Z.Text.PC.Internal.myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression':\n"
        , "  invalid-regex-representation-is-given, regex-representation=" ++ shows regex_representation ".\n"
        ]
    go :: [RegEx] -> ParserBase LocChr String
    go [regex] = mkPB (maybe [] pure . takeStringMatchedWithRegexFromStreamByMaximalMunchRule regex)
    go _ = error myErrMsg
