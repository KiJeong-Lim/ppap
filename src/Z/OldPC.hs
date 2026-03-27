module Z.OldPC where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import Z.Algorithms
import Z.Doc
import Z.Utils hiding (calcTab)

newtype PM a
    = PM { unPM :: ReadS a }
    deriving ()

instance Functor PM where
    fmap a2b p1 = PM $ \str0 -> [ (a2b a, str1) | (a, str1) <- unPM p1 str0 ]

instance Applicative PM where
    pure a = PM $ \str0 -> [(a, str0)]
    p1 <*> p2 = PM $ \str0 -> [ (a2b a, str2) | (a2b, str1) <- unPM p1 str0, (a, str2) <- unPM p2 str1 ]

instance Monad PM where
    -- return = PM . curry return
    p1 >>= p2 = PM (unPM p1 >=> uncurry (unPM . p2))

instance Alternative PM where
    empty = PM (pure mempty)
    p1 <|> p2 = PM (pure mappend <*> unPM p1 <*> unPM p2)

instance MonadPlus PM where

instance MonadFail PM where
    fail = const empty

instance Semigroup (PM a) where
    p1 <> p2 = p1 <|> p2

instance Monoid (PM a) where
    mempty = empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM $ \str -> if null str then [] else let ch = head str in if condition ch then [(ch, tail str)] else []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []

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
    findShortest = head . mSort ((<=) `on` length)
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
type Row = Int

type Col = Int

type LocChr = ((Row, Col), Char)

type LocStr = [LocChr]

type Src = String

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

calcTab :: Int -> Int
calcTab n = 4 & (\my_tab_width -> my_tab_width - n `mod` my_tab_width)

addLoc :: Src -> LocStr
addLoc = foldr (\ch -> \kont -> uncurry $ \r -> \c -> r `seq` c `seq` (((r, c), ch) : kont (getNextRow r ch, getNextCol c ch))) (const []) <*> pure (initRow, initCol) where
    getNextRow :: Row -> Char -> Row
    getNextRow r '\n' = succ r
    getNextRow r _ = r
    getNextCol :: Col -> Char -> Col
    getNextCol c '\n' = initCol
    getNextCol c '\t' = c + calcTab (c - initCol)
    getNextCol c _ = succ c

makeMessageForParsingError :: FilePath -> Src -> LocStr -> ErrMsg
makeMessageForParsingError path src lstr = renderDoc theMsgDoc where
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
        [ text path <> text ":" <> (textbf (show stuckRow)) <> text ":" <> (textbf (show stuckCol)) <> text ": error:"
        , text "parse error " <> (if null lstr then text "at EOF" else text "on input `" <> text (dispatchChar (snd (head lstr))) <> text "'")
        , hcat
            [ vcat
                [ text ""
                , hcat
                    [ text " "
                    , (textbf (show stuckRow))
                    , text " "
                    ]
                , text ""
                ]
            , beam '|'
            , vcat
                [ text " "
                , text " " <> text stuckLine
                , text " " <> text (replicate (stuckCol - initCol) ' ') <> text "^"
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

type PC = MyPC

execPC :: PC val -> Src -> Either LocStr val
execPC p str = execPB (unMyPC p) (addLoc str)

runPC :: FilePath -> PC val -> Src -> Either ErrMsg val
runPC path p src = either (callWithStrictArg Left . makeMessageForParsingError path src) (callWithStrictArg return) (execPC p src)

acceptPC :: (Char -> Bool) -> PC Char
acceptPC = MyPC . mkPB . go where
    go :: (Char -> Bool) -> LocStr -> [(Char, LocStr)]
    go cond lstr = [ (ch, drop 1 lstr) | (_, ch) <- take 1 lstr, cond ch ]

consumePC :: String -> PC ()
consumePC = mapM_ acceptPC . map (==)

matchPC :: String -> PC ()
matchPC = MyPC . go where
    go :: String -> PB LocChr ()
    go expecteds = mkPB $ \lstr0 -> case splitAt (length expecteds) lstr0 of
        (token, lstr1) -> if map snd token == expecteds then one ((), lstr1) else []

eofPC :: PC ()
eofPC = MyPC go where
    go :: PB LocChr ()
    go = mkPB $ \lstr0 -> if null lstr0 then one ((), lstr0) else []

regexPC :: RegExRep -> PC String
regexPC = myAtomicParserCombinatorReturningLongestStringMatchedWithGivenRegularExpression

intPC :: PC Int
intPC = pure read <*> regexPC "['-']? ['0'-'9']+"

negPC :: PC val -> PC ()
negPC p1 = do
    p1_passed <- (p1 *> return True) /> return False
    if p1_passed then empty else return ()

acceptQuote :: PC String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\\\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'\\\'\\\\\'])* \"\\\"\""

skipWhite :: PC Int
skipWhite = MyPC go where
    go :: PB LocChr Int
    go = mkPB $ \lstr0 -> case span (\lch -> snd lch == ' ') lstr0 of
        (ws, lstr1) -> one (length ws, lstr1)

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

dispatchChar :: Char -> String
dispatchChar '\"' = "\\\""
dispatchChar '\'' = "\\\'"
dispatchChar '\\' = "\\\\"
dispatchChar '\t' = "\\t"
dispatchChar '\n' = "\\n"
dispatchChar '\r' = "\\r"
dispatchChar '\f' = "\\f"
dispatchChar ch = [ch]
