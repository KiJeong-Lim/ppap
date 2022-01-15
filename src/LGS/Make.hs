module LGS.Make where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LGS.Util
import Y.Base
import Z.Algo.Function

theCsUniv :: Set.Set Char
theCsUniv = Set.fromList (['a' .. 'z'] ++ ['A' .. 'Z'] ++ " `~0123456789!@#$%^&*()-=_+[]\\{}|;\':\"\n,./<>?")

runCharSet :: CharSet -> Set.Set Char
runCharSet = go where
    go :: CharSet -> Set.Set Char
    go (CsSingle ch) = Set.singleton ch
    go (CsEnum ch1 ch2) = Set.fromAscList [ch1 .. ch2]
    go (chs1 `CsUnion` chs2) = go chs1 `Set.union` go chs2
    go (chs1 `CsDiff` chs2) = go chs1 `Set.difference` go chs2
    go CsUniv = theCsUniv

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
    loop ReZero = do
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

reduceRegEx :: RegEx -> RegEx
reduceRegEx = reduceRegExOldPassion

makeJumpRegexTable :: DFA -> Map.Map (ParserS, ParserS) RegEx
makeJumpRegexTable (DFA q0 qfs delta markeds pseudo_finals) = Map.fromAscList [ ((q_from, q_to), theClosure `lookTable` (q_from, q_to)) | q_from <- qs, q_to <- qs ] where
    lookTable :: Map.Map (ParserS, ParserS) RegEx -> (ParserS, ParserS) -> RegEx
    lookTable table = maybe ReZero id . flip Map.lookup table
    qs :: [ParserS]
    qs = Set.toAscList theSetOfAllStatesInDFA where
        theSetOfAllStatesInDFA :: Set.Set ParserS
        theSetOfAllStatesInDFA = Set.unions
            [ Set.singleton q0
            , Map.keysSet qfs
            , Set.unions [ Set.fromList [q, p] | ((q, ch), p) <- Map.toAscList delta ]
            , Set.unions (map snd (Map.elems markeds))
            , pseudo_finals
            ]
    makeRegExFromCharSet :: (Char -> Bool) -> RegEx
    makeRegExFromCharSet cond
        | length nos < 5 = mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
        | otherwise = foldr mkReUnion mkReZero
            [ case pair of
                (ch1, ch2) -> if ch1 == ch2 then mkReWord [ch1] else mkReCharSet (mkCsEnum ch1 ch2)
            | pair <- foldr loop [] yess
            ]
        where
            loop :: Char -> [(Char, Char)] -> [(Char, Char)]
            loop ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                ([], pairs1) -> (ch0, ch0) : pairs1
                ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
            mypartition :: ([Char], [Char])
            mypartition = List.partition cond (Set.toDescList theCsUniv)
            yess :: [Char]
            yess = fst mypartition
            nos :: [Char]
            nos = snd mypartition
    theClosure :: Map.Map (ParserS, ParserS) RegEx
    theClosure = Map.fromAscList (recNat myBase myStep (length qs))
    myBase :: [((ParserS, ParserS), RegEx)]
    myBase = do
        q_i <- qs
        q_j <- qs
        case reduceRegEx (mkReUnion (if q_i == q_j then mkReWord [] else mkReZero) (makeRegExFromCharSet (\ch -> Map.lookup (q_i, ch) delta == Just q_j))) of
            ReZero -> []
            re -> return ((q_i, q_j), re)
    myStep :: ParserS -> [((ParserS, ParserS), RegEx)] -> [((ParserS, ParserS), RegEx)]
    myStep k prev = do
        let q_k = qs !! k
            table = Map.fromAscList prev
        q_i <- qs
        q_j <- qs
        case reduceRegEx (mkReUnion (table `lookTable` (q_i, q_j)) (mkReConcat (table `lookTable` (q_i, q_k)) (mkReConcat (mkReStar (table `lookTable` (q_k, q_k))) (table `lookTable` (q_k, q_j))))) of
            ReZero -> []
            re -> return ((q_i, q_j), re)

generateRegexTable :: DFA -> Map.Map ParserS RegEx
generateRegexTable dfa = Map.fromList mymap where
    theJumpRegexTable :: Map.Map (ParserS, ParserS) RegEx
    theJumpRegexTable = makeJumpRegexTable dfa
    mymap :: [(ParserS, RegEx)]
    mymap = do
        ((q_from, q_to), path_of_regex) <- Map.toAscList theJumpRegexTable
        if q_from == getInitialQOfDFA dfa
            then return
                ( q_to
                , elaborateRegEx path_of_regex
                )
            else []
    elaborateRegEx :: RegEx -> RegEx
    elaborateRegEx = step2 . step1 where
        unfoldConcat :: RegEx -> [RegEx]
        unfoldConcat (ReConcat re1 re2) = unfoldConcat re1 ++ unfoldConcat re2
        unfoldConcat re = [re]
        matchPrefix :: [RegEx] -> [RegEx] -> Maybe [RegEx]
        matchPrefix [] res = Just res
        matchPrefix (re1 : res2) (re3 : res4) = if re1 == re3 then matchPrefix res2 res4 else Nothing
        matchPrefix _ _ = Nothing
        step1 :: RegEx -> [RegEx]
        step1 = go [] . unfoldConcat where
            go :: [RegEx] -> [RegEx] -> [RegEx]
            go acc []
                = reverse acc
            go acc (re1 : res2)
                | ReStar re3 <- re1
                = case matchPrefix (reverse (unfoldConcat re3)) acc of
                    Nothing -> go (re1 : acc) res2
                    Just acc_suffix -> go (mkReDagger re3 : acc_suffix) res2
                | otherwise
                = go (re1 : acc) res2
        step2 :: [RegEx] -> RegEx
        step2 = List.foldl' mkReConcat mkReEpsilon . concat . map go where
            go :: RegEx -> [RegEx]
            go (ReQuest re1) = step2aux1 (unfoldConcat re1)
            go re = [re]
            isStar :: RegEx -> Bool
            isStar (ReStar _) = True
            isStar _ = False
            isQuest :: RegEx -> Bool
            isQuest (ReQuest _) = True
            isQuest _ = False
            step2aux1 :: [RegEx] -> [RegEx]
            step2aux1 res1 = distributeQuest (filter (not . isStar) res1) where
                distributeQuest :: [RegEx] -> [RegEx]
                distributeQuest [re2] = [ if isStar re3 then re3 else mkReQuest re2 | re3 <- res1 ]
                distributeQuest res2 = if all isQuest res2 then res1 else [mkReQuest (List.foldl' mkReConcat mkReEpsilon res1)]

reduceRegExOldPassion :: RegEx -> RegEx
reduceRegExOldPassion = myMain where
    differentiate :: RegEx -> Char -> RegEx
    differentiate (ReZero) ch = mkReZero
    differentiate (ReUnion re1 re2) ch = mkReUnion (differentiate re1 ch) (differentiate re2 ch)
    differentiate (ReWord str1) ch = if null str1 then mkReZero else if head str1 == ch then mkReWord (tail str1) else mkReZero
    differentiate (ReConcat re1 re2) ch = mkReUnion (mkReConcat (differentiate re1 ch) re2) (if isNullable re1 then differentiate re2 ch else mkReZero)
    differentiate (ReStar re1) ch = mkReConcat (differentiate re1 ch) (mkReStar re1)
    differentiate (ReDagger re1) ch = differentiate (mkReConcat re1 (mkReStar re1)) ch
    differentiate (ReQuest re1) ch = differentiate (mkReUnion re1 (mkReWord [])) ch
    differentiate (ReCharSet chs1) ch = if ch `Set.member` runCharSet chs1 then mkReWord [] else mkReZero
    runRegEx :: RegEx -> String -> Bool
    runRegEx = curry (isNullable . uncurry (List.foldl' differentiate))
    isNullable :: RegEx -> Bool
    isNullable (ReZero) = False
    isNullable (ReUnion re1 re2) = isNullable re1 || isNullable re2
    isNullable (ReWord str1) = null str1
    isNullable (ReConcat re1 re2) = isNullable re1 && isNullable re2
    isNullable (ReStar re1) = True
    isNullable (ReDagger re1) = isNullable re1
    isNullable (ReQuest re1) = True
    isNullable (ReCharSet chs1) = False
    implies :: RegEx -> RegEx -> Bool
    implies = go where
        go :: RegEx -> RegEx -> Bool
        go re1 re2 = re1 == re2 || dispatch re1 re2
        dispatch :: RegEx -> RegEx -> Bool
        dispatch (ReZero) re1 = True
        dispatch (ReUnion re1 re2) re3 = re1 `implies` re3 && re2 `implies` re3
        dispatch (ReWord str1) re2 = runRegEx re2 str1
        dispatch (ReCharSet chs1) (ReCharSet chs2) = runCharSet chs1 `Set.isSubsetOf` runCharSet chs2
        dispatch (ReCharSet chs1) (ReWord [ch2]) = runCharSet chs1 `Set.isSubsetOf` Set.singleton ch2
        dispatch (ReStar re1) (ReStar re2) = re1 `implies` re2
        dispatch (ReStar re1) (ReDagger re2) = isNullable re2 && re1 `implies` ReStar re2
        dispatch (ReStar re1) (ReQuest re2) = ReStar re1 `implies` re2
        dispatch (ReDagger re1) (ReStar re2) = re1 `implies` re2
        dispatch (ReDagger re1) (ReDagger re2) = re1 `implies` re2
        dispatch (ReDagger re1) (ReQuest re2) = ReStar re1 `implies` re2
        dispatch (ReQuest re1) (ReStar re2) = re1 `implies` ReStar re2
        dispatch (ReQuest re1) (ReDagger re2) = isNullable re2 && re1 `implies` ReStar re2
        dispatch (ReQuest re1) (ReQuest re2) = re1 `implies` re2
        dispatch (ReConcat re1 re2) (ReStar re3) = re1 `implies` ReStar re3 && re2 `implies` ReStar re3
        dispatch (ReConcat re1 re2) (ReDagger re3) = (re1 `implies` ReDagger re3 && re2 `implies` ReStar re3) || (re1 `implies` ReStar re3 && re2 `implies` ReDagger re3)
        dispatch re1 (ReUnion re2 re3) = re1 `implies` re2 || re1 `implies` re3
        dispatch re1 (ReStar re2) = re1 `implies` ReWord [] || re1 `implies` re2
        dispatch re1 (ReDagger re2) = re1 `implies` re2
        dispatch re1 (ReQuest re2) = re1 `implies` ReWord [] || re1 `implies` re2
        dispatch re1 re2 = False
    equiv :: RegEx -> RegEx -> Bool
    re1 `equiv` re2 = re1 `implies` re2 && re2 `implies` re1
    dropLast :: [x] -> [x]
    dropLast [] = []
    dropLast [x1] = []
    dropLast (x1 : xs) = x1 : dropLast xs
    unfoldConcat :: RegEx -> [RegEx]
    unfoldConcat (ReConcat re1 re2) = unfoldConcat re1 ++ unfoldConcat re2
    unfoldConcat (ReWord []) = []
    unfoldConcat re1 = [re1]
    myMain :: RegEx -> RegEx
    myMain = go3 . go2 . go1 where
        extractCS :: [Char] -> RegEx
        extractCS chs
            = case reverse (foldr loop1 [] chs) of
                [] -> mkReZero
                pair : pairs -> case foldr mkCsUnion (loop2 pair) (map loop2 pairs) of
                    CsSingle ch -> mkReWord [ch]
                    chs' -> mkReCharSet chs'
            where
                loop1 :: Char -> [(Char, Char)] -> [(Char, Char)]
                loop1 ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                    ([], pairs1) -> (ch0, ch0) : pairs1
                    ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
                loop2 :: (Char, Char) -> CharSet
                loop2 (ch1, ch2) = if ch1 == ch2 then mkCsSingle ch1 else mkCsEnum ch1 ch2
        go1 :: RegEx -> RegEx
        go1 (ReZero) = makeReZero1
        go1 (ReUnion re1 re2) = makeReUnion1 (go1 re1) (go1 re2)
        go1 (ReWord str1) = makeReWord1 str1
        go1 (ReConcat re1 re2) = makeReConcat1 (go1 re1) (go1 re2)
        go1 (ReStar re1) = makeReStar1 (go1 re1)
        go1 (ReDagger re1) = makeReDagger1 (go1 re1)
        go1 (ReQuest re1) = makeReQuest1 (go1 re1)
        go1 (ReCharSet chs1) = makeReCharSet1 chs1
        makeReZero1 :: RegEx
        makeReZero1 = mkReZero
        makeReUnion1 :: RegEx -> RegEx -> RegEx
        makeReUnion1 re1 re2
            | ReCharSet chs1 <- re1
            , ReCharSet chs2 <- re2
            = makeReCharSet1 (mkCsUnion chs1 chs2)
            | re1 `implies` re2
            = re2
            | re2 `implies` re1
            = re1
            | ReUnion re3 re4 <- re2
            = mkReUnion (mkReUnion re1 re3) re4
            | otherwise
            = mkReUnion re1 re2
        makeReWord1 :: String -> RegEx
        makeReWord1 str1
            = case str1 of
                [ch1] -> mkReCharSet (mkCsSingle ch1)
                str1' -> mkReWord str1'
        makeReConcat1 :: RegEx -> RegEx -> RegEx
        makeReConcat1 re1 re2
            | ReConcat re3 re4 <- re2
            = mkReConcat (mkReConcat re1 re3) re4
            | otherwise
            = mkReConcat re1 re2
        makeReStar1 :: RegEx -> RegEx
        makeReStar1 re1
            = case deleteUnit re1 of
                ReZero -> mkReWord []
                re2 -> case destructStarConcat re2 of
                    [] -> mkReStar re2
                    re3 : res4 -> mkReStar (List.foldl' mkReUnion re3 res4)
            where
                deleteUnit :: RegEx -> RegEx
                deleteUnit (ReUnion re1 (ReWord [])) = deleteUnit re1
                deleteUnit (ReUnion re1 re2) = mkReUnion (deleteUnit re1) re2
                deleteUnit (ReWord []) = ReZero
                deleteUnit re1 = re1
                destructStarConcat :: RegEx -> [RegEx]
                destructStarConcat (ReStar re1)
                    = [re1]
                destructStarConcat (ReConcat re1 (ReStar re2))
                    = case destructStarConcat re1 of
                        [] -> []
                        res3 -> res3 ++ [re2]
                destructStarConcat re1
                    = []
        makeReDagger1 :: RegEx -> RegEx
        makeReDagger1 = makeReConcat1 <*> makeReStar1
        makeReQuest1 :: RegEx -> RegEx
        makeReQuest1 re1 = makeReUnion1 (makeReWord1 []) re1
        makeReCharSet1 :: CharSet -> RegEx
        makeReCharSet1 (CsUnion chs1 chs2)
            = case (runCharSet chs1, runCharSet chs2) of
                (chs1_val, chs2_val)
                    | chs1_val `Set.isSubsetOf` chs2_val -> mkReCharSet chs2
                    | chs2_val `Set.isSubsetOf` chs1_val -> mkReCharSet chs1
                    | otherwise -> case List.partition (\ch -> ch `Set.member` chs1_val || ch `Set.member` chs2_val) (Set.toDescList theCsUniv) of
                        (yess, nos)
                            | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                            | otherwise -> extractCS yess
        makeReCharSet1 chs1
            = extractCS (Set.toAscList (runCharSet chs1))
        go2 :: RegEx -> RegEx
        go2 (ReZero) = makeReZero2
        go2 (ReUnion re1 re2) = makeReUnion2 (go2 re1) (go2 re2)
        go2 (ReWord str1) = makeReWord2 str1
        go2 (ReConcat re1 re2) = makeReConcat2 (go2 re1) (go2 re2)
        go2 (ReStar re1) = makeReStar2 (go2 re1)
        go2 (ReDagger re1) = makeReDagger2 (go2 re1)
        go2 (ReCharSet chs1) = makeReCharSet2 chs1
        makeReZero2 :: RegEx
        makeReZero2 = mkReZero
        makeReUnion2 :: RegEx -> RegEx -> RegEx
        makeReUnion2 re1 re2
            | ReDagger re3 <- re1
            , ReWord [] <- re2
            = mkReStar re3
            | ReWord [] <- re1
            , ReDagger re3 <- re2
            = mkReStar re3
            | ReStar re3 <- re1
            , ReWord [] <- re2
            = re1
            | ReWord [] <- re1
            , ReStar re3 <- re2
            = re2
            | ReQuest re3 <- re1
            , ReWord [] <- re2
            = re1
            | ReWord [] <- re1
            , ReQuest re3 <- re2
            = re2
            | ReWord [] <- re1
            = mkReQuest re2
            | ReWord [] <- re2
            = mkReQuest re1
            | otherwise
            = makeReUnion1 re1 re2
        makeReWord2 :: String -> RegEx
        makeReWord2 = mkReWord
        makeReConcat2 :: RegEx -> RegEx -> RegEx
        makeReConcat2 re1 re2
            | ReWord str1 <- re1
            , ReWord str2 <- re2
            = mkReWord (str1 ++ str2)
            | ReStar re3 <- re1
            , ReStar re4 <- re2
            , re3 `equiv` re4
            = re1
            | ReStar re3 <- re1
            , ReDagger re4 <- re2
            , re3 `equiv` re4
            = re2
            | ReStar re3 <- re1
            , ReQuest re4 <- re2
            , re3 `equiv` re4
            = re1
            | ReDagger re3 <- re1
            , ReStar re4 <- re2
            , re3 `equiv` re4
            = re1
            | ReDagger re3 <- re1
            , ReQuest re4 <- re2
            , re3 `equiv` re4
            = re1
            | ReQuest re3 <- re1
            , ReStar re4 <- re2
            , re3 `equiv` re4
            = re2
            | ReQuest re3 <- re1
            , ReDagger re4 <- re2
            , re3 `equiv` re4
            = re2
            | ReStar re3 <- re1
            , re2 `equiv` re3
            = mkReDagger re3
            | ReStar re3 <- re2
            , re1 `equiv` re3
            = mkReDagger re3
            | ReConcat re3 re4 <- re1
            = case makeReConcat2 re4 re2 of
                ReConcat re5 re6 -> makeReConcat1 (makeReConcat2 re3 re5) re6
                re5 -> makeReConcat2 re3 re5
            | otherwise
            = makeReConcat1 re1 re2
        makeReStar2 :: RegEx -> RegEx
        makeReStar2 = mkReStar
        makeReDagger2 :: RegEx -> RegEx
        makeReDagger2 = mkReDagger
        makeReQuest2 :: RegEx -> RegEx
        makeReQuest2 = mkReQuest
        makeReCharSet2 :: CharSet -> RegEx
        makeReCharSet2 chs1
            = case List.partition (\ch -> ch `Set.member` runCharSet chs1) (Set.toDescList theCsUniv) of
                (yess, nos)
                    | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                    | otherwise -> case reverse (mkCollection yess) of
                        [] -> mkReZero
                        re1 : res2 -> case List.foldl' mkCsUnion re1 res2 of
                            CsSingle ch3 -> ReWord [ch3]
                            chs3 -> mkReCharSet chs3
            where
                loop :: Char -> [(Char, Char)] -> [(Char, Char)]
                loop ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                    ([], pairs1) -> (ch0, ch0) : pairs1
                    ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
                mkCollection :: [Char] -> [CharSet]
                mkCollection yess = do
                    (ch1, ch2) <- foldr loop [] yess
                    if ch1 == ch2
                        then return (mkCsSingle ch1)
                        else return (mkCsEnum ch1 ch2)
        makeReZero3 :: RegEx
        makeReZero3 = mkReZero
        makeReUnion3 :: RegEx -> RegEx -> RegEx
        makeReUnion3 re1 re2
            | ReQuest re3 <- re1
            = mkReQuest (makeReUnion3 re3 re2)
            | ReQuest re3 <- re2
            = mkReQuest (makeReUnion3 re1 re3)
            | ReUnion re3 re4 <- re1
            = case makeReUnion3 re4 re2 of
                ReUnion re5 re6 -> makeReUnion2 (makeReUnion3 re3 re5) re6
                re5 -> makeReUnion3 re3 re5
            | otherwise
            = case go (unfoldConcat re1) (unfoldConcat re2) of
                Nothing -> makeReUnion2 re1 re2
                Just re3 -> re3
            where
                go :: [RegEx] -> [RegEx] -> Maybe RegEx
                go res1 res2
                    | null res1 || null res2 = return (tryToMerge res1 res2)
                    | Just res3 <- head res1 `matchPrefix` res2 = do
                        re4 <- go (tail res1) res3
                        return (mkReConcat (head res1) re4)
                    | Just res3 <- last res1 `matchSuffix` res2 = do
                        re4 <- go (dropLast res1) res3
                        return (mkReConcat re4 (last res1))
                    | otherwise = Nothing
                tryToMerge :: [RegEx] -> [RegEx] -> RegEx
                tryToMerge [] [] = makeReWord2 []
                tryToMerge [] (re1 : res2) = makeReQuest2 (List.foldl' makeReConcat2 re1 res2)
                tryToMerge (re1 : res2) [] = makeReQuest2 (List.foldl' makeReConcat2 re1 res2)
                tryToMerge (re1 : res2) (re3 : res4) = makeReUnion2 (List.foldl' makeReConcat2 re1 res2) (List.foldl' makeReConcat2 re3 res4)
        makeReWord3 :: String -> RegEx
        makeReWord3 = mkReWord
        makeReConcat3 :: RegEx -> RegEx -> RegEx
        makeReConcat3 = makeReConcat2
        makeReStar3 :: RegEx -> RegEx
        makeReStar3 re0
            | ReConcat re1 re2 <- re0
            = case foldr loop1 init1 (unfoldConcat re1 ++ unfoldConcat re2) of
                Nothing -> makeReStar2 (mkReConcat re1 re2)
                Just (re3', res4) -> case (re3', res4) of
                    (Nothing, []) -> mkReWord []
                    (Nothing, re5 : res6) -> mkReStar (List.foldl' makeReUnion3 re5 res6)
                    (Just re5, res6) -> mkReStar (List.foldl' makeReUnion1 re5 res6)
            | otherwise
            = makeReStar2 re0
            where
                init1 :: Maybe (Maybe RegEx, [RegEx])
                init1 = Just (Nothing, [])
                loop1 :: RegEx -> Maybe (Maybe RegEx, [RegEx]) -> Maybe (Maybe RegEx, [RegEx])
                loop1 (ReStar re1) acc = do
                    (re2', res3) <- acc
                    return (re2', re1 : res3)
                loop1 re1 acc = do
                    (re2', res3) <- acc
                    case re2' of
                        Nothing -> return (Just re1, res3)
                        Just re2 -> Nothing
        makeReDagger3 :: RegEx -> RegEx
        makeReDagger3 = mkReDagger
        makeReQuest3 :: RegEx -> RegEx
        makeReQuest3 = mkReQuest
        makeReCharSet3 :: CharSet -> RegEx
        makeReCharSet3 = mkReCharSet
        go3 :: RegEx -> RegEx
        go3 (ReZero) = makeReZero3
        go3 (ReUnion re1 re2) = makeReUnion3 (go3 re1) (go3 re2)
        go3 (ReWord str1) = makeReWord3 str1
        go3 (ReConcat re1 re2) = makeReConcat3 (go3 re1) (go3 re2)
        go3 (ReStar re1) = makeReStar3 (go3 re1)
        go3 (ReDagger re1) = makeReDagger3 (go3 re1)
        go3 (ReQuest re1) = makeReQuest3 (go3 re1)
        go3 (ReCharSet chs1) = makeReCharSet3 chs1
        matchPrefix :: RegEx -> [RegEx] -> Maybe [RegEx]
        matchPrefix re1 res2 = if re1 `equiv` head res2 then return (tail res2) else Nothing
        matchSuffix :: RegEx -> [RegEx] -> Maybe [RegEx]
        matchSuffix re1 res2 = if re1 `equiv` last res2 then return (dropLast res2) else Nothing
