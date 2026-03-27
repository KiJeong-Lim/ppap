module LGS.Alpha1 where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Doc
import Z.Algorithms
import Z.OldPC (PC, consumePC, smallid, charPC, acceptQuote, largeid, skipWhite, lend, indent, regexPC, eofPC, runPC)
import Z.System
import Z.Utils

type ParserS = Int

type CharSetVar = String

type RegExVar = String

type HsCode = [String]

type CharSetEnv = Map.Map CharSetVar CharSet

type RegExEnv = Map.Map RegExVar RegEx

type ExitNumber = Int

data CharSet
    = CsVar CharSetVar
    | CsSingle Char
    | CsEnum Char Char
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsUniv
    deriving (Eq, Show)

data RegEx
    = ReVar RegExVar
    | ReZero
    | ReUnion RegEx RegEx
    | ReWord String
    | ReConcat RegEx RegEx
    | ReStar RegEx
    | ReDagger RegEx
    | ReQuest RegEx
    | ReCharSet CharSet
    deriving (Eq, Show)

data NFA
    = NFA
        { getInitialQOfNFA :: !(ParserS)
        , getFinalQsOfNFA :: !(Map.Map ParserS ExitNumber)
        , getTransitionsOfNFA :: !(Map.Map (ParserS, Maybe Char) (Set.Set ParserS))
        , getMarkedQsOfNFA :: !(Map.Map ParserS (Bool, ParserS))
        , getPseudoFinalsOfNFA :: !(Map.Map ExitNumber ParserS)
        }
    deriving (Eq)

data DFA
    = DFA
        { getInitialQOfDFA :: !(ParserS)
        , getFinalQsOfDFA :: !(Map.Map ParserS ExitNumber)
        , getTransitionsOfDFA :: !(Map.Map (ParserS, Char) ParserS)
        , getMarkedQsOfDFA :: !(Map.Map ParserS (Bool, Set.Set ParserS))
        , getPseudoFinalsOfDFA :: !(Set.Set ParserS)
        }
    deriving (Eq)

data RightContext
    = NilRCtx
    | PosRCtx RegEx
    | OddRCtx RegEx
    | NegRCtx RegEx
    deriving (Eq, Show)

data XBlock
    = HsHead HsCode
    | HsTail HsCode
    | CsVDef CharSetVar CharSet
    | ReVDef RegExVar RegEx
    | XMatch (RegEx, RightContext) (Maybe HsCode)
    | Target { getTokenType :: String, getLexerName :: String }
    deriving (Show)

instance Outputable CharSet where
    pprint 0 (CsDiff chs1 chs2) = pprint 0 chs1 . strstr " \\ " . pprint 2 chs2
    pprint 0 chs = pprint 1 chs
    pprint 1 (CsUnion chs1 chs2) = pprint 1 chs1 . strstr " " . pprint 2 chs2
    pprint 1 chs = pprint 2 chs
    pprint 2 (CsVar var) = strstr "$" . strstr var
    pprint 2 (CsSingle ch1) = formalChar ch1
    pprint 2 (CsEnum ch1 ch2) = formalChar ch1 . strstr "-" . formalChar ch2
    pprint 2 (CsUniv) = strstr "."
    pprint 2 chs = pprint 3 chs
    pprint _ chs = strstr "(" . pprint 0 chs . strstr ")"

instance Outputable RegEx where
    pprint 0 (ReUnion re1 re2) = pprint 0 re1 . strstr " + " . pprint 1 re2
    pprint 0 re = pprint 1 re
    pprint 1 (ReConcat re1 re2) = pprint 1 re1 . strstr " " . pprint 2 re2
    pprint 1 re = pprint 2 re
    pprint 2 (ReStar re1) = pprint 2 re1 . strstr "*"
    pprint 2 (ReDagger re1) = pprint 2 re1 . strstr "+"
    pprint 2 (ReQuest re1) = pprint 2 re1 . strstr "?"
    pprint 2 re = pprint 3 re
    pprint 3 (ReCharSet chs1) = strstr "[" . pprint 0 chs1 . strstr "]"
    pprint 3 (ReWord str1) = pprintString str1
    pprint 3 (ReZero) = strstr "()"
    pprint 3 (ReVar var) = strstr "$" . strstr var
    pprint 3 re = pprint 4 re
    pprint _ re = strstr "(" . pprint 0 re . strstr ")"

formalChar :: Char -> ShowS
formalChar '\"' = strstr "\'\\\"\'"
formalChar ch = showsPrec 0 ch

readCharSet :: PC CharSet
readCharSet = go 0 where
    go :: Int -> PC CharSet
    go 0 = mconcat
        [ List.foldl' CsDiff <$> go 1 <*> many (consumePC " \\ " *> go 2)
        , go 1
        ]
    go 1 = mconcat
        [ CsUnion <$> go 2 <* consumePC " " <*> go 1
        , go 2
        ]
    go 2 = mconcat
        [ (CsVar <$ consumePC "$") <*> smallid
        , CsSingle <$> charPC
        , CsEnum <$> charPC <* consumePC "-" <*> charPC
        , consumePC "." $> CsUniv
        , go 3
        ]
    go _ = consumePC "(" *> go 0 <* consumePC ")"

readRegEx :: PC RegEx
readRegEx = go 0 where
    suffix :: PC (RegEx -> RegEx)
    suffix = mconcat
        [ consumePC "+" $> ReDagger
        , consumePC "*" $> ReStar
        , consumePC "?" $> ReQuest
        ]
    go :: Int -> PC RegEx
    go 0 = List.foldl' ReUnion <$> go 1 <*> many (consumePC " + " *> go 1)
    go 1 = List.foldl' ReConcat <$> go 2 <*> many (consumePC " " *> go 2)
    go 2 = List.foldl' (flip ($)) <$> go 3 <*> many suffix
    go 3 = mconcat
        [ consumePC "[" *> (ReCharSet <$> readCharSet) <* consumePC "]"
        , ReWord <$> acceptQuote
        , consumePC "()" $> ReZero
        , (ReVar <$ consumePC "$") <*> largeid
        , go 4
        ]
    go _ = consumePC "(" *> go 0 <* consumePC ")"

readBlock :: PC XBlock
readBlock = mconcat
    [ do
        consumePC "\\hshead"
        skipWhite
        consumePC "{"
        lend
        hshead <- many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend $> ""))
        consumePC "}"
        lend
        return (HsHead hshead)
    , do
        consumePC "\\hstail"
        skipWhite
        consumePC "{"
        lend
        hstail <- many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend $> ""))
        consumePC "}"
        lend
        return (HsTail hstail)
    , do
        consumePC "\\define"
        skipWhite
        consumePC "$"
        csv <- smallid
        skipWhite
        consumePC "="
        skipWhite
        cs <- readCharSet
        lend
        return (CsVDef csv cs)
    , do
        consumePC "\\define"
        skipWhite
        consumePC "$"
        rev <- largeid
        skipWhite
        consumePC "="
        skipWhite
        re <- readRegEx
        lend
        return (ReVDef rev re)
    , do
        consumePC "\\xmatch"
        skipWhite
        regex <- readRegEx
        right_ctx <- mconcat
            [ do
                consumePC " +/ "
                PosRCtx <$> readRegEx
            , do
                consumePC " / "
                OddRCtx <$> readRegEx
            , return NilRCtx
            ]
        skipWhite
        consumePC ":"
        skipWhite
        maybe_hscode <- mconcat
            [ do
                consumePC "skip"
                lend
                return Nothing
            , do
                lend
                hscode <- many (indent 4 *> regexPC "[.\\'\n']*" <* lend)
                return (Just hscode)
            ]
        return (XMatch (regex, right_ctx) maybe_hscode)
    , do
        consumePC "\\target"
        skipWhite
        consumePC "{"
        lend
        indent 4 *> consumePC "token-type:"
        skipWhite
        token_type <- acceptQuote
        lend
        indent 4 *> consumePC "lexer-name:"
        skipWhite
        lexer_name <- acceptQuote
        lend
        consumePC "}"
        lend
        return $ Target
            { getTokenType = token_type
            , getLexerName = lexer_name
            }
    ]

theCsUniv :: Set.Set Char
theCsUniv = Set.fromList (['a' .. 'z'] ++ ['A' .. 'Z'] ++ " `~0123456789!@#$%^&*()-=_+[]\\{}|;\':\"\n,./<>?")

runCharSet :: CharSet -> Set.Set Char
runCharSet = go where
    go :: CharSet -> Set.Set Char
    go (CsSingle ch) = Set.singleton ch
    go (CsEnum ch1 ch2) = Set.fromAscList [ch1 .. ch2]
    go (chs1 `CsUnion` chs2) = go chs1 `Set.union` go chs2
    go (chs1 `CsDiff` chs2) = go chs1 `Set.difference` go chs2
    go (CsUniv) = theCsUniv

mkstrict :: (a, b) -> (a, b)
mkstrict pair = fst pair `seq` snd pair `seq` pair

getUnitedNFAfromREs :: [(RegEx, RightContext)] -> NFA
getUnitedNFAfromREs = runIdentity . go where
    getNewQ :: StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ParserS
    getNewQ = do
        (maximumOfQs, deltas) <- get
        put (maximumOfQs + 1, deltas)
        return maximumOfQs
    drawTransition :: ((ParserS, Maybe Char), ParserS) -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ()
    drawTransition (key, q) = do
        (maximumOfQs, deltas) <- get
        case Map.lookup key deltas of
            Nothing -> put (maximumOfQs, Map.insert key (Set.singleton q) deltas)
            Just qs -> put (maximumOfQs, Map.update (const (Just (Set.insert q qs))) key deltas)
    loop :: RegEx -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity (ParserS, ParserS)
    loop (ReUnion regex1 regex2) = do
        (qi1, qf1) <- loop regex1
        (qi2, qf2) <- loop regex2
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qi, Nothing), qi2)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qf2, Nothing), qf)
        return (qi, qf)
    loop (ReConcat regex1 regex2) = do
        (qi1, qf1) <- loop regex1
        (qi2, qf2) <- loop regex2
        drawTransition ((qf1, Nothing), qi2)
        return (qi1, qf2)
    loop (ReStar regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qi, Nothing), qf)
        return (qi, qf)
    loop (ReZero) = do
        qi <- getNewQ
        qf <- getNewQ
        return (qi, qf)
    loop (ReWord str) = do
        let n = length str
        qs <- mapM (\_ -> getNewQ) [0, 1 .. n]
        mapM drawTransition (zip (zip (take n qs) (map Just str)) (drop 1 qs))
        return (qs !! 0, qs !! n)
    loop (ReCharSet chs) = do
        qi <- getNewQ
        qf <- getNewQ
        mapM drawTransition (zip (zip (repeat qi) (map Just (Set.toList (runCharSet chs)))) (repeat qf))
        return (qi, qf)
    loop (ReDagger regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        return (qi, qf)
    loop (ReQuest regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qi, Nothing), qf)
        return (qi, qf)
    go :: [(RegEx, RightContext)] -> Identity NFA
    go xmatch_defns = do
        let q0 = 0
            n = length xmatch_defns
        (pragments, (numberOfQs, deltas)) <- flip runStateT (n + 1, Map.empty) $ sequence
            [ case right_ctx of
                NilRCtx -> do
                    let qf = label
                    (qi1, qf1) <- loop regex1
                    drawTransition ((q0, Nothing), qi1)
                    drawTransition ((qf1, Nothing), qf)
                    return ((qf, label), (Nothing, Nothing))
                PosRCtx regex2 -> do
                    let qf = label
                    (qi1, qf1) <- loop regex1
                    (qi2, qf2) <- loop regex2
                    qw <- getNewQ
                    drawTransition ((q0, Nothing), qi1)
                    drawTransition ((qf1, Nothing), qw)
                    drawTransition ((qw, Nothing), qi2)
                    drawTransition ((qf2, Nothing), qf)
                    return ((qf, label), (Nothing, Just (label, (True, qw))))
                OddRCtx regex2 -> do
                    let qf = label
                    (qi1, qf1) <- loop regex1
                    (qi2, qf2) <- loop regex2
                    qw <- getNewQ
                    drawTransition ((q0, Nothing), qi1)
                    drawTransition ((qf1, Nothing), qw)
                    drawTransition ((qw, Nothing), qi2)
                    drawTransition ((qf2, Nothing), qf)
                    return ((qf, label), (Nothing, Just (label, (False, qw))))
                NegRCtx regex2 -> do
                    let qf = label
                    (qi1, qf1) <- loop regex1
                    (qi2, qf2) <- loop regex2
                    qw <- getNewQ
                    drawTransition ((q0, Nothing), qi1)
                    drawTransition ((qf1, Nothing), qf)
                    drawTransition ((qf, Nothing), qi2)
                    drawTransition ((qf2, Nothing), qw)
                    return ((qf, label), (Just (label, qw), Nothing))
            | (label, (regex1, right_ctx)) <- zip [1, 2 .. n] xmatch_defns
            ]
        return $ NFA
            { getInitialQOfNFA = q0
            , getFinalQsOfNFA = Map.fromList (map fst pragments)
            , getTransitionsOfNFA = deltas
            , getMarkedQsOfNFA = Map.fromList [ my_item | Just my_item <- map (snd . snd) pragments ]
            , getPseudoFinalsOfNFA = Map.fromList [ my_item | Just my_item <- map (fst . snd) pragments ]
            }

makeDFAfromNFA :: NFA -> DFA
makeDFAfromNFA (NFA q0 qfs deltas markeds pseudo_finals) = runIdentity result where
    eClosure :: Set.Set ParserS -> Set.Set ParserS
    eClosure qs = if qs == qs' then qs' else eClosure qs' where
        qs' :: Set.Set ParserS
        qs' = foldr Set.union qs
            [ case Map.lookup (q, Nothing) deltas of
                Nothing -> Set.empty
                Just ps -> ps
            | q <- Set.toList qs
            ]
    getNexts :: Set.Set ParserS -> Char -> Set.Set ParserS
    getNexts qs ch = Set.unions
        [ case Map.lookup (q, Just ch) deltas of
            Nothing -> Set.empty
            Just ps -> ps
        | q <- Set.toList qs
        ]
    drawGraph :: Map.Map (Set.Set ParserS) ParserS -> [((Set.Set ParserS, ParserS), Char)] -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map (Set.Set ParserS) ParserS)
    drawGraph mapOldToNew [] = return mapOldToNew
    drawGraph mapOldToNew (((qs, q'), ch) : triples) = do
        let ps = eClosure (getNexts qs ch)
        deltas' <- get
        case Map.lookup ps mapOldToNew of
            Nothing -> do
                let p' = Map.size mapOldToNew
                put (Map.insert (q', ch) p' deltas')
                drawGraph (Map.insert ps p' mapOldToNew) triples
            Just p' -> do
                put (Map.insert (q', ch) p' deltas')
                drawGraph mapOldToNew triples
    bangbang :: Map.Map (Set.Set ParserS) ParserS -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map ParserS ExitNumber, Map.Map (Set.Set ParserS) ParserS)
    bangbang mapOldToNew = do
        mapOldToNew' <- drawGraph mapOldToNew ((,) <$> Map.toList mapOldToNew <*> Set.toList theCsUniv)
        let addItem (qf, label) = if and [ maybe True (\q -> not (q `Set.member` qs)) (Map.lookup label pseudo_finals) | (qs, p) <- Map.toList mapOldToNew', p == qf ] then Map.alter (Just . maybe label (min label)) qf else id
        if mapOldToNew == mapOldToNew'
            then return
                ( foldr addItem Map.empty
                    [ (p, label)
                    | (q, label) <- Map.toList qfs
                    , (qs, p) <- Map.toList mapOldToNew'
                    , q `Set.member` qs
                    ]
                , mapOldToNew'
                )
            else bangbang mapOldToNew'
    result :: Identity DFA
    result = do
        let new_q0 = 0
        ((new_qfs, wanted_map), new_deltas) <- runStateT (bangbang (Map.singleton (eClosure (Set.singleton q0)) new_q0)) Map.empty
        return $ DFA
            { getInitialQOfDFA = new_q0
            , getFinalQsOfDFA = new_qfs
            , getTransitionsOfDFA = new_deltas
            , getMarkedQsOfDFA = Map.fromAscList
                [ mkstrict
                    ( i
                    , mkstrict
                        ( b
                        , Set.fromList
                            [ p
                            | (qs, p) <- Map.toList wanted_map
                            , q `Set.member` qs
                            ]
                        )
                    )
                | (i, (b, q)) <- Map.toAscList markeds
                ]
            , getPseudoFinalsOfDFA = Set.fromList
                [ p
                | (label, q) <- Map.toList pseudo_finals
                , not (q `Set.member` Map.keysSet new_qfs)
                , (qs, p) <- Map.toList wanted_map
                , q `Set.member` qs
                ]
            }

makeMinimalDFA :: DFA -> DFA
makeMinimalDFA (DFA q0 qfs deltas markeds pseudo_finals) = result where
    theSetOfAllStates :: Set.Set ParserS
    theSetOfAllStates = Set.unions
        [ Set.singleton q0
        , Map.keysSet qfs
        , Set.map fst (Map.keysSet deltas)
        , Set.fromList (Map.elems deltas)
        , Set.unions (map snd (Map.elems markeds))
        , pseudo_finals
        ]
    theCharSet :: Set.Set Char
    theCharSet = Set.map snd (Map.keysSet deltas)
    initialKlasses :: [Set.Set ParserS]
    initialKlasses = filter (not . Set.null) theList where
        theList :: [Set.Set ParserS]
        theList = concat
            [ [theSetOfAllStates `Set.difference` (pseudo_finals `Set.union` Map.keysSet qfs), pseudo_finals]
            , Map.elems (foldr loop1 Map.empty (Map.toList qfs))
            ]
        loop1 :: (ParserS, ExitNumber) -> Map.Map ExitNumber (Set.Set ParserS) -> Map.Map ExitNumber (Set.Set ParserS)
        loop1 (qf, label) = Map.alter (Just . maybe (Set.singleton qf) (Set.insert qf)) label
    finalKlasses :: [Set.Set ParserS]
    finalKlasses = splitKlasses initialKlasses initialKlasses where
        splitKlasses :: [Set.Set ParserS] -> [Set.Set ParserS] -> [Set.Set ParserS]
        splitKlasses result stack
            | null stack = result
            | otherwise = uncurry splitKlasses (Set.foldr (uncurry . loop1 (head stack)) (result, tail stack) theCharSet)
        loop1 :: Set.Set ParserS -> Char -> [Set.Set ParserS] -> [Set.Set ParserS] -> ([Set.Set ParserS], [Set.Set ParserS])
        loop1 top ch = foldr (>=>) return . map loop2 where
            focused :: Set.Set ParserS
            focused = Set.filter (\q -> maybe False (\p -> p `Set.member` top) (Map.lookup (q, ch) deltas)) theSetOfAllStates
            loop2 :: Set.Set ParserS -> [Set.Set ParserS] -> ([Set.Set ParserS], [Set.Set ParserS])
            loop2 klass stack
                | Set.null myintersection = ([klass], stack)
                | Set.null mydifference = ([klass], stack)
                | otherwise = mkstrict
                    ( [myintersection, mydifference]
                    , case klass `List.elemIndex` stack of
                        Nothing -> if Set.size myintersection <= Set.size mydifference then myintersection : stack else mydifference : stack
                        Just idx -> [myintersection, mydifference] ++ take idx stack ++ drop (idx + 1) stack
                    )
                where
                    myintersection :: Set.Set ParserS
                    myintersection = klass `Set.intersection` focused
                    mydifference :: Set.Set ParserS
                    mydifference = klass `Set.difference` focused
    convert :: ParserS -> ParserS
    convert q = head
        [ q'
        | (q', qs) <- zip [0, 1 .. ] finalKlasses
        , q `Set.member` qs
        ]
    result :: DFA
    result = DFA
        { getInitialQOfDFA = convert q0
        , getFinalQsOfDFA = Map.fromList
            [ (convert qf, label)
            | (qf, label) <- Map.toList qfs
            ]
        , getTransitionsOfDFA = Map.fromList
            [ ((convert q, ch), convert p)
            | ((q, ch), p) <- Map.toList deltas
            ]
        , getMarkedQsOfDFA = Map.map (fmap (Set.map convert)) markeds
        , getPseudoFinalsOfDFA = Set.map convert pseudo_finals
        }

deleteDeadStates :: DFA -> DFA
deleteDeadStates (DFA q0 qfs deltas markeds pseudo_finals) = result where
    edges :: Map.Map ParserS (Set.Set ParserS)
    edges = foldr go Map.empty [ (p, q) | ((q, ch), p) <- Map.toList deltas ] where
        go :: (ParserS, ParserS) -> Map.Map ParserS (Set.Set ParserS) -> Map.Map ParserS (Set.Set ParserS)
        go (p, q) = Map.alter (Just . maybe (Set.singleton q) (Set.insert q)) p
    winners :: Set.Set ParserS
    winners = go (Set.toAscList (pseudo_finals `Set.union` Map.keysSet qfs)) Set.empty where
        go :: [ParserS] -> Set.Set ParserS -> Set.Set ParserS
        go [] ps = ps
        go (q : qs) ps = if q `Set.member` ps then go qs ps else go (maybe [] Set.toAscList (Map.lookup q edges) ++ qs) (Set.insert q ps)
    result :: DFA
    result = DFA
        { getInitialQOfDFA = q0
        , getFinalQsOfDFA = qfs
        , getTransitionsOfDFA = Map.fromAscList
            [ ((q, ch), p)
            | ((q, ch), p) <- Map.toAscList deltas
            , q `Set.member` winners
            , p `Set.member` winners
            ]
        , getMarkedQsOfDFA = Map.map (fmap (Set.filter (\q -> q `Set.member` winners))) markeds
        , getPseudoFinalsOfDFA = Set.filter (\q -> q `Set.member` winners) pseudo_finals
        }

makeDFAfromREs :: [(RegEx, RightContext)] -> DFA
makeDFAfromREs = deleteDeadStates . makeMinimalDFA . makeDFAfromNFA . getUnitedNFAfromREs

mkCsSingle :: Char -> CharSet
mkCsSingle ch1 = ch1 `seq` CsSingle ch1

mkCsEnum :: Char -> Char -> CharSet
mkCsEnum ch1 ch2 = ch1 `seq` ch2 `seq` CsEnum ch1 ch2

mkCsUnion :: CharSet -> CharSet -> CharSet
mkCsUnion chs1 chs2 = chs1 `seq` chs2 `seq` CsUnion chs1 chs2

mkCsDiff :: CharSet -> CharSet -> CharSet
mkCsDiff chs1 chs2 = chs1 `seq` chs2 `seq` CsDiff chs1 chs2

mkCsUniv :: CharSet
mkCsUniv = CsUniv

mkReZero :: RegEx
mkReZero = ReZero

mkReUnion :: RegEx -> RegEx -> RegEx
mkReUnion (ReZero) re1 = re1
mkReUnion re1 (ReZero) = re1
mkReUnion re1 re2 = ReUnion re1 re2

mkReWord :: String -> RegEx
mkReWord str = str `seq` ReWord str

mkReConcat :: RegEx -> RegEx -> RegEx
mkReConcat (ReZero) re1 = ReZero
mkReConcat re1 (ReZero) = ReZero
mkReConcat (ReWord str1) (ReWord str2) = mkReWord (str1 ++ str2)
mkReConcat (ReWord []) re1 = re1
mkReConcat re1 (ReWord []) = re1
mkReConcat re1 re2 = ReConcat re1 re2

mkReStar :: RegEx -> RegEx
mkReStar (ReZero) = mkReEpsilon
mkReStar (ReWord []) = mkReEpsilon
mkReStar (ReStar re1) = mkReStar re1
mkReStar (ReDagger re1) = mkReStar re1
mkReStar (ReQuest re1) = mkReStar re1
mkReStar re1 = ReStar re1

mkReDagger :: RegEx -> RegEx
mkReDagger (ReZero) = mkReZero
mkReDagger (ReWord []) = mkReEpsilon
mkReDagger (ReStar re1) = mkReStar re1
mkReDagger (ReDagger re1) = mkReDagger re1
mkReDagger (ReQuest re1) = mkReStar re1
mkReDagger re1 = ReDagger re1

mkReQuest :: RegEx -> RegEx
mkReQuest (ReZero) = mkReEpsilon
mkReQuest (ReWord []) = mkReEpsilon
mkReQuest (ReStar re1) = mkReStar re1
mkReQuest (ReDagger re1) = mkReStar re1
mkReQuest (ReQuest re1) = mkReQuest re1
mkReQuest re1 = ReQuest re1

mkReCharSet :: CharSet -> RegEx
mkReCharSet chs = chs `seq` ReCharSet chs

mkReEpsilon :: RegEx
mkReEpsilon = ReWord []

generateRegexTable :: DFA -> Map.Map ParserS RegEx
generateRegexTable = const Map.empty

modifyCSinRE :: (CharSet -> ExceptT ErrMsg Identity CharSet) -> (RegEx -> ExceptT ErrMsg Identity RegEx)
modifyCSinRE modify = go where
    go :: RegEx -> ExceptT ErrMsg Identity RegEx
    go (ReVar var) = pure (ReVar var)
    go ReZero = pure ReZero
    go (regex1 `ReUnion` regex2) = pure ReUnion <*> go regex1 <*> go regex2
    go (ReWord word) = pure (ReWord word)
    go (regex1 `ReConcat` regex2) = pure ReConcat <*> go regex1 <*> go regex2
    go (ReStar regex1) = pure ReStar <*> go regex1
    go (ReDagger regex1) = pure ReDagger <*> go regex1
    go (ReQuest regex1) = pure ReQuest <*> go regex1
    go (ReCharSet chs) = pure ReCharSet <*> modify chs

substituteCS :: CharSetEnv -> CharSet -> ExceptT ErrMsg Identity CharSet
substituteCS env = go where
    go :: CharSet -> ExceptT ErrMsg Identity CharSet
    go (CsVar var) = maybe (throwE ("`substituteCS': couldn't find the variable ``$" ++ var ++ "'' in the environment `" ++ show env ++ "'.")) return (Map.lookup var env)
    go (CsSingle ch) = pure (CsSingle ch)
    go (CsEnum ch1 ch2) = pure (CsEnum ch1 ch2)
    go (chs1 `CsUnion` chs2) = pure CsUnion <*> go chs1 <*> go chs2
    go (chs1 `CsDiff` chs2) = pure CsDiff <*> go chs1 <*> go chs2
    go CsUniv = pure CsUniv

substituteRE :: RegExEnv -> RegEx -> ExceptT ErrMsg Identity RegEx
substituteRE env = go where
    go :: RegEx -> ExceptT ErrMsg Identity RegEx
    go (ReVar var) = maybe (throwE ("`substituteRE': couldn't find the variable ``$" ++ var ++ "'' in the environment `" ++ show env ++ "'.")) return (Map.lookup var env)
    go ReZero = pure ReZero
    go (regex1 `ReUnion` regex2) = pure ReUnion <*> go regex1 <*> go regex2
    go (ReWord word) = pure (ReWord word)
    go (regex1 `ReConcat` regex2) = pure ReConcat <*> go regex1 <*> go regex2
    go (ReStar regex1) = pure ReStar <*> go regex1
    go (ReDagger regex1) = pure ReDagger <*> go regex1
    go (ReQuest regex1) = pure ReQuest <*> go regex1
    go (ReCharSet chs) = pure (ReCharSet chs)

overlap :: String -> String -> String
overlap str1 str2 = case (length str1, length str2) of
    (n1, n2) -> if n1 >= n2 then take (n1 - n2) str1 ++ str2 else str2

genLexer :: [XBlock] -> ExceptT ErrMsg Identity [String]
genLexer xblocks = do
    (_, chs_env) <- flip runStateT Map.empty $ sequence
        [ do
            env <- get
            chs' <- lift (substituteCS env chs)
            put (Map.insert var chs' env)
        | CsVDef var chs <- xblocks
        ]
    (_, re_env) <- flip runStateT Map.empty $ sequence
        [ do
            env <- get
            re' <- lift (substituteRE env re)
            put (Map.insert var re' env)
        | ReVDef var re <- xblocks
        ]
    theDFA <- fmap makeDFAfromREs $ sequence
        [ case right_ctx of
            NilRCtx -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                return (regex1'', NilRCtx)
            PosRCtx regex2 -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                regex2' <- substituteRE re_env regex2
                regex2'' <- modifyCSinRE (substituteCS chs_env) regex2'
                return (regex1'', PosRCtx regex2'')
            OddRCtx regex2 -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                regex2' <- substituteRE re_env regex2
                regex2'' <- modifyCSinRE (substituteCS chs_env) regex2'
                return (regex1'', OddRCtx regex2'')
            NegRCtx regex2 -> do
                regex1' <- substituteRE re_env regex1
                regex1'' <- modifyCSinRE (substituteCS chs_env) regex1'
                regex2' <- substituteRE re_env regex2
                regex2'' <- modifyCSinRE (substituteCS chs_env) regex2'
                return (regex1'', NegRCtx regex2'')
        | XMatch (regex1, right_ctx) _ <- xblocks
        ]
    (token_type, lexer_name) <- case [ (token_type, lexer_name) | Target token_type lexer_name <- xblocks ] of
        [pair] -> return pair
        _ -> throwE "A target must exist unique."
    hshead <- case [ hscode | HsHead hscode <- xblocks ] of
        [hscode] -> return hscode
        _ -> throwE "A hshead must exist unique."
    hstail <- case [ hscode | HsTail hscode <- xblocks ] of
        [hscode] -> return hscode
        _ -> throwE "A hstail must exist unique."
    ((), x_out) <- runWriterT $ do
        let _this = lexer_name ++ "_this"
            theRegexTable = generateRegexTable theDFA
            theMaxLen = length (show (maybe 0 fst (Set.maxView (Map.keysSet theRegexTable))))
            tellLine string_stream = tell [string_stream "\n"]
        tellLine (ppunc "\n" (map strstr hshead))
        tellLine (strstr "import qualified Control.Monad.Trans.State.Strict as XState")
        tellLine (strstr "import qualified Data.Functor.Identity as XIdentity")
        tellLine (strstr "import qualified Data.Map.Strict as XMap")
        tellLine (strstr "import qualified Data.Set as XSet")
        tellLine (ppunc "\n" (strstr "" : map strstr hstail))
        if null hstail then return () else tellLine (strstr "")
        tellLine (strstr "-- the following codes are generated by LGS.")
        if getInitialQOfDFA theDFA `Set.member` Map.keysSet (getFinalQsOfDFA theDFA) then tellLine (strstr "-- Warning: The empty string is acceptable!") else return ()
        tellLine (strstr "")
        tellLine (strstr "data DFA")
        tellLine (strstr "    = DFA")
        tellLine (strstr "        { getInitialQOfDFA :: Int")
        tellLine (strstr "        , getFinalQsOfDFA :: XMap.Map Int Int")
        tellLine (strstr "        , getTransitionsOfDFA :: XMap.Map (Int, Char) Int")
        tellLine (strstr "        }")
        tellLine (strstr "    deriving ()")
        tellLine (strstr "")
        tellLine (strstr lexer_name . strstr " :: String -> Either (Int, Int) [" . strstr token_type . strstr "]")
        tellLine (strstr lexer_name . strstr " = " . strstr _this . strstr " . addLoc 1 1 where")
        tellLine (strstr "    theDFA :: DFA")
        tellLine (strstr "    theDFA = DFA")
        tellLine (strstr "        { getInitialQOfDFA = " . shows (getInitialQOfDFA theDFA))
        tellLine (strstr "        , getFinalQsOfDFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . shows q . strstr ", " . shows p . strstr ")" | (q, p) <- Map.toAscList (getFinalQsOfDFA theDFA) ] . strstr "]")
        tellLine (strstr "        , getTransitionsOfDFA = XMap.fromAscList " . plist 12 [ ppunc ", " [ strstr "((" . shows q . strstr ", " . shows ch . strstr "), " . shows p . strstr ")" | ((q, ch), p) <- deltas ] | deltas <- splitUnless (\x1 -> \x2 -> fst (fst x1) == fst (fst x2)) (Map.toAscList (getTransitionsOfDFA theDFA)) ])
        tellLine (strstr "        }")
        tellLine (strstr "    runDFA :: DFA -> [((Int, Int), Char)] -> Either (Int, Int) ((Maybe Int, [((Int, Int), Char)]), [((Int, Int), Char)])")
        tellLine (strstr "    runDFA (DFA q0 qfs deltas) = Right . XIdentity.runIdentity . runFast where")
        tellLine (strstr "        loop1 :: Int -> [((Int, Int), Char)] -> [((Int, Int), Char)] -> XState.StateT (Maybe Int, [((Int, Int), Char)]) XIdentity.Identity [((Int, Int), Char)]")
        tellLine (strstr "        loop1 q buffer [] = return buffer")
        tellLine (strstr "        loop1 q buffer (ch : str) = do")
        tellLine (strstr "            (latest, accepted) <- XState.get")
        tellLine (strstr "            case XMap.lookup (q, snd ch) deltas of")
        tellLine (strstr "                Nothing -> return (buffer ++ [ch] ++ str)")
        tellLine (strstr "                Just p -> case XMap.lookup p qfs of")
        tellLine (strstr "                    Nothing -> loop1 p (buffer ++ [ch]) str")
        tellLine (strstr "                    latest' -> do")
        tellLine (strstr "                        XState.put (latest', accepted ++ buffer ++ [ch])")
        tellLine (strstr "                        loop1 p [] str")
        tellLine (strstr "        runFast :: [((Int, Int), Char)] -> XIdentity.Identity ((Maybe Int, [((Int, Int), Char)]), [((Int, Int), Char)])")
        tellLine (strstr "        runFast input = do")
        tellLine (strstr "            (rest, (latest, accepted)) <- XState.runStateT (loop1 q0 [] input) (Nothing, [])")
        tellLine (strstr "            return ((latest, accepted), rest)")
        tellLine (strstr "    addLoc :: Int -> Int -> String -> [((Int, Int), Char)]")
        tellLine (strstr "    addLoc _ _ [] = []")
        tellLine (strstr "    addLoc row col (ch : chs) = if ch == '\\n' then ((row, col), ch) : addLoc (row + 1) 1 chs else ((row, col), ch) : addLoc row (col + 1) chs")
        tellLine (strstr "    " . strstr _this . strstr " :: [((Int, Int), Char)] -> Either (Int, Int) [" . strstr token_type . strstr "]")
        tellLine (strstr "    " . strstr _this . strstr " [] = return []")
        tellLine (strstr "    " . strstr _this . strstr " str0 = do")
        tellLine (strstr "        let return_one my_token = return [my_token]")
        tellLine (strstr "        dfa_output <- runDFA theDFA str0")
        tellLine (strstr "        (str1, piece) <- case dfa_output of")
        tellLine (strstr "            ((_, []), _) -> Left (fst (head str0))")
        tellLine (strstr "            ((Just label, accepted), rest) -> return (rest, ((label, map snd accepted), (fst (head accepted), fst (head (reverse accepted)))))")
        tellLine (strstr "            _ -> Left (fst (head str0))")
        tellLine (strstr "        tokens1 <- case piece of")
        let destructors = [ destructor | XMatch _ destructor <- xblocks ]
        sequence
            [ case destructor of
                Just [hscode] -> do
                    tellLine (strstr "            ((" . shows label . strstr ", this), ((row1, col1), (row2, col2))) -> return_one (" . strstr hscode . strstr ")")
                    return ()
                Just (hscode : hscodes) -> do
                    tellLine (strstr "            ((" . shows label . strstr ", this), ((row1, col1), (row2, col2))) -> return_one $ " . strstr hscode)
                    tellLine (ppunc "\n" [ strstr "            " . strstr str | str <- hscodes ])
                    return ()
                _ -> do
                    tellLine (strstr "            ((" . shows label . strstr ", this), ((row1, col1), (row2, col2))) -> return []")
                    return ()
            | (label, destructor) <- zip [1, 2 .. length destructors] destructors
            ]
        tellLine (strstr "        tokens2 <- " . strstr _this . strstr " str1")
        tellLine (strstr "        return (tokens1 ++ tokens2)")
        return ()
    return x_out

main :: IO ()
main = do
    dir <- shelly ("LGS =<< ")
    let dir_rev = reverse dir
    let dir' = if take 4 dir_rev == "txt." then reverse (drop 4 dir_rev) else dir
    x_src <- readFileNow dir
    case maybe (Left ("cannot open file: " ++ dir)) (runPC dir (many (readBlock <* many lend) <* eofPC)) x_src of
        Left err -> putStrLn err
        Right xblocks -> case runIdentity (runExceptT (genLexer xblocks)) of
            Left err -> do
                writeFileNow (dir' ++ ".failed") err
                shelly ("LGS >>= tell (generating-failed)")
                return ()
            Right delta -> do
                writeFileNow (dir' ++ ".hs") delta
                shelly ("LGS >>= tell (the-lexer-has-been-generated)")
                return ()
