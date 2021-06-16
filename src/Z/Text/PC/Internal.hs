module Z.Text.PC.Internal where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import Z.Algo.Sorting
import Test.QuickCheck
import Z.Text.Doc
import Z.Text.PC.Base
import Z.Text.PM
import Z.Utils

type Row = Int

type Col = Int

type Loc = (Row, Col)

type LocChr = (Loc, Char)

type LocStr = [LocChr]

type Src = String

type ErrMsg = String

type RegExRep = String

data CharSet
    = CsUniv
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsEnum Char Char
    | CsSingle Char
    deriving ()

data RegEx
    = ReCSet CharSet
    | ReWord String
    | RePlus RegEx RegEx
    | ReZero
    | ReMult RegEx RegEx
    | ReStar RegEx
    deriving ()

newtype P val
    = PC { unPC :: ParserBase LocChr val }
    deriving ()

instance Functor P where
    fmap a2b = PC . fmap a2b . unPC

instance Applicative P where
    pure = PC . pure
    p1 <*> p2 = PC (unPC p1 <*> unPC p2)

instance Monad P where
    p1 >>= p2 = PC (unPC p1 >>= unPC . p2)

instance Alternative P where
    empty = PC empty
    p1 <|> p2 = PC (unPC p1 <|> unPC p2)

instance MonadPlus P where

instance Semigroup (P val) where
    p1 <> p2 = PC (unPC p1 <> unPC p2)

instance Monoid (P val) where
    mempty = PC mempty

instance Read CharSet where
    readsPrec = unPM . go where
        go :: Int -> PM CharSet
        go 0 = List.foldl' mkCsDiff <$> go 1 <*> many (consumeStr "\\" *> go 2)
        go 1 = List.foldl' mkCsUnion <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = mconcat
            [ mkCsSingle <$> autoPM 0
            , mkCsEnum <$> autoPM 0 <* consumeStr "-" <*> autoPM 0
            , consumeStr "." *> pure mkCsUniv
            , go 3
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

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

mkCsUniv :: CharSet
mkCsUniv = CsUniv

mkCsUnion :: CharSet -> CharSet -> CharSet
mkCsUnion chs1 chs2 = chs1 `seq` chs2 `seq` CsUnion chs1 chs2

mkCsDiff :: CharSet -> CharSet -> CharSet
mkCsDiff chs1 chs2 = chs1 `seq` chs2 `seq` CsDiff chs1 chs2

mkCsEnum :: Char -> Char -> CharSet
mkCsEnum ch1 ch2 = ch1 `seq` ch2 `seq` CsEnum ch1 ch2

mkCsSingle :: Char -> CharSet
mkCsSingle ch = ch `seq` CsSingle ch

mkReCSet :: CharSet -> RegEx
mkReCSet chs = chs `seq` ReCSet chs

mkReWord :: String -> RegEx
mkReWord str = str `seq` ReWord str

mkRePlus :: RegEx -> RegEx -> RegEx
mkRePlus re1 re2 = re1 `seq` re2 `seq` RePlus re1 re2

mkReZero :: RegEx
mkReZero = ReZero

mkReMult :: RegEx -> RegEx -> RegEx
mkReMult re1 re2 = re1 `seq` re2 `seq` ReMult re1 re2

mkReStar :: RegEx -> RegEx
mkReStar re1 = re1 `seq` ReStar re1

addLoc :: Src -> LocStr
addLoc = go 1 1 where
    getNextRow :: Row -> Char -> Row
    getNextRow r '\n' = r + 1
    getNextRow r _ = r
    getNextCol :: Col -> Char -> Col
    getNextCol c '\n' = 1
    getNextCol c '\t' = c + calcTab (c - 1)
    getNextCol c _ = c + 1
    go :: Row -> Col -> String -> LocStr
    go r c [] = []
    go r c (ch : str) = ((r, c), ch) : go (getNextRow r ch) (getNextCol c ch) str

mkErrMsg :: Src -> LocStr -> ErrMsg
mkErrMsg src lstr = show theMsg where
    stuckRow :: Row
    stuckRow = case lstr of
        [] -> length (filter (\lch -> snd lch == '\n') lstr) + 1
        ((r, c), _) : _ -> r
    stuckLine :: Src
    stuckLine = splitBy '\n' src !! (stuckRow - 1)
    stuckCol :: Col
    stuckCol = case lstr of
        [] -> length stuckLine + 1
        ((r, c), _) : _ -> c
    theMsg :: Doc
    theMsg = vcat
        [ hcat
            [ vcat
                [ pstr ""
                , pcat
                    [ pstr " "
                    , pprint stuckRow
                    , pstr " "
                    ]
                , pstr ""
                ]
            , beam '|'
            , vcat
                [ pstr ""
                , pstr " " +> pstr stuckLine
                , pstr (replicate stuckCol ' ') +> pstr "^"
                ]
            ]
        , pstr ""
        , if null lstr
            then pstr "?- parsing error at EOF."
            else pstr "?- parsing error at " +> pprint stuckRow +> pstr ":" +> pprint stuckCol +> pstr "."
        ]

runRegEx :: LocStr -> RegEx -> (LocStr, String)
runRegEx = flip (curry go) "" where
    runCharSet :: CharSet -> Char -> Bool
    runCharSet (CsUniv) ch = True
    runCharSet (CsUnion chs1 chs2) ch = runCharSet chs1 ch || runCharSet chs2 ch
    runCharSet (CsDiff ch1 ch2) ch = runCharSet ch1 ch && not (runCharSet ch2 ch)
    runCharSet (CsEnum ch1 ch2) ch = ch1 <= ch && ch <= ch2
    runCharSet (CsSingle ch1) ch = ch == ch1
    isNullable :: RegEx -> Bool
    isNullable (ReCSet chs) = False
    isNullable (ReWord str) = null str
    isNullable (RePlus re1 re2) = isNullable re1 || isNullable re2
    isNullable (ReZero) = False
    isNullable (ReMult re1 re2) = isNullable re1 && isNullable re2
    isNullable (ReStar re1) = True
    differentiate :: Char -> RegEx -> RegEx
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
        | isNullable re1 = mkRePlus (mkReMult (differentiate ch re1) re2) (differentiate ch re2)
        | otherwise = mkReMult (differentiate ch re1) re2
    differentiate ch (ReStar re1)
        = mkReMult (differentiate ch re1) (mkReStar re1)
    isNotEmpty :: CharSet -> Bool
    isNotEmpty _ = True
    mayPlvsVltra :: RegEx -> Bool
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
                then return (reverse output, regex)
                else fail "It is impossible that I read the buffer further more and then accept the given regex."
            ((_, ch) : buffer') -> do
                let regex' = differentiate ch regex
                    output' = ch : output
                put buffer'
                if isNullable regex'
                    then return (reverse output', regex')
                    else if mayPlvsVltra regex'
                        then repeatPlvsVltra output' regex'
                        else fail "It is impossible that I read the buffer further more and then accept the given regex."
    go :: (LocStr, String) -> RegEx -> (LocStr, String)
    go last_commit current_regex
        = case runStateT (repeatPlvsVltra "" current_regex) (getBuffer last_commit) of
            Nothing -> last_commit
            Just ((fresh_output, next_regex), new_buffer) ->
                let new_commit = (new_buffer, getOutput last_commit ++ fresh_output) in
                if null new_buffer
                    then new_commit
                    else go new_commit next_regex
        where
            getBuffer :: (LocStr, String) -> LocStr
            getBuffer = fst
            getOutput :: (LocStr, String) -> String
            getOutput = snd

parserOfRegularExpression :: RegExRep -> P String
parserOfRegularExpression regex_representation = PC (go maybeRegEx) where
    maybeRegEx :: Maybe RegEx
    maybeRegEx = case [ regex | (regex, "") <- readsPrec 0 regex_representation ] of
        [regex] -> Just regex
        _ -> Nothing
    go :: Maybe RegEx -> ParserBase LocChr String
    go Nothing = error ("In `Z.Text.PC.Internal.parserOfRegularExpression': input-regex-is-invalid, input-regex=`" ++ regex_rep ++ "'.")
    go (Just regex) = PAct $ \lstr0 -> case runRegEx lstr0 regex of
        (lstr1, str) -> PAlt [(PVal str, lstr1)]
