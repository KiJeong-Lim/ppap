module PGS.Make where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Function
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import PGS.Util
import Y.Base
import Z.Algo.Function
import Z.Algo.Sorting
import Z.Utils

import Data.Maybe (isJust, isNothing, fromMaybe)
import Data.Foldable

instance Outputable Associativity where
    pprint _ ALeft = strstr "left"
    pprint _ ARight = strstr "right"
    pprint _ ANone = strstr "none"

instance Outputable NSym where
    pprint 0 (NSApp ns1 ns2) = pprint 0 ns1 . strstr " " . pprint 1 ns2
    pprint 0 ns1 = pprint 1 ns1
    pprint 1 (NSVar nsv) = strstr nsv
    pprint 1 ns1 = pprint 2 ns1
    pprint _ ns1 = strstr "(" . pprint 0 ns1 . strstr ")"

instance Outputable TSym where
    pprint _ (TSEOF) = strstr "\\$"
    pprint _ (TSVar tsv) = strstr tsv

instance Outputable Sym where
    pprint _ (NS ns) = strstr "<" . pprint 0 ns . strstr ">"
    pprint _ (TS ts) = strstr "`" . pprint 0 ts . strstr "\'"

instance Outputable CFGrammar where
    pprint _ (CFGrammar start terminals productions) = strcat
        [ strstr "start-symbol: " . pprint 0 (NS start) . nl
        , strstr "terminal-symbols: " . plist 2 [ pprint 0 (TS t) . strstr " : " . pprint 0 assoc . strstr ", " . strstr (reverse (take 2 ("0" ++ reverse (show prec)))) | (t, (assoc, prec)) <- Map.toList terminals ] . nl
        , strstr "production-rules: " . plist 2 [ pprint 0 (NS lhs) . strstr " ::= " . ppunc " " (map (pprint 0) rhs) . strstr "; " . strstr (reverse (take 2 (reverse ("0" ++ show prec)))) | ((lhs, rhs), prec) <- Map.toList productions ] . nl
        ]

instance Outputable LR0Item where
    pprint _ (LR0Item lhs left right) = pprint 0 (NS lhs) . strstr " ::= " . ppunc " " (map (pprint 0) left ++ [strstr "."] ++ map (pprint 0) right)

instance Outputable Cannonical0 where
    pprint _ (Cannonical0 vertices root edges)
        = ppunc "\n"
            [ strstr "getParserSInfo :: ParserS -> ParserSInfo"
            , ppunc "\n"
                [ ppunc "\n"
                    [ strstr "getParserSInfo " . shows q . strstr " = ParserSInfo"
                    , strstr "    { myItems = " . plist 8 (map (quotify . pprint 0) items)
                    , strstr "    , myNexts = " . plist 8 [ quotify (pprint 0 sym . strstr " +-> " . shows p) | (sym, p) <- maybe [] id (lookup q formatedEdges) ]
                    , strstr "    }"
                    ]
                | (q, items) <- formatedVertices
                ]
            ]
        where
            formatedVertices :: [(ParserS, [LR0Item])]
            formatedVertices = do
                (items, q) <- sortByMerging (\pair1 -> \pair2 -> snd pair1 < snd pair2) (Map.toAscList vertices)
                return
                    ( q
                    , Set.toAscList items
                    )
            formatedEdges :: [(ParserS, [(Sym, ParserS)])]
            formatedEdges = do
                triples <- splitUnless (\triple1 -> \triple2 -> fst (fst triple1) == fst (fst triple2)) (Map.toAscList edges)
                case triples of
                    [] -> []
                    ((q, sym), p) : triples' -> return
                        ( q
                        , sortByMerging (\pair1 -> \pair2 -> snd pair1 < snd pair2) ((sym, p) : [ (sym', p') | ((q', sym'), p') <- triples' ])
                        )

instance Outputable Action where
    pprint _ (Shift p) = strstr "SHIFT: " . shows p . strstr ";"
    pprint _ (Reduce (lhs, rhs)) = strstr "REDUCE: <" . pprint 0 lhs . strstr "> ::= " . ppunc " " (map (pprint 0) rhs) . strstr ";"
    pprint _ (Accept) = strstr "ACCEPT;"

instance Outputable LR1Parser where
    pprint _ (LR1Parser initS actionT reduceT) = strcat
        [ strstr "initS: " . shows initS . nl
        , strstr "actionT: " . plist 2 [ strstr "(" . shows q . strstr ", " . pprint 0 (TS t) . strstr ") +-> " . pprint 0 action | ((q, t), action) <- Map.toList actionT ] . nl
        , strstr "reduceT: " . plist 2 [ strstr "(" . shows q . strstr ", " . pprint 0 (NS nt) . shows p | ((q, nt), p) <- Map.toList reduceT ] . nl
        ]

makeCollectionAndLALR1Parser :: CFGrammar -> ExceptT Conflict Identity (Cannonical0, LR1Parser)
makeCollectionAndLALR1Parser (CFGrammar start terminals productions) = theResult where
    maxPrec :: Precedence
    maxPrec = 100
    start' :: NSym
    start' = NSVar "\\ACCEPT"
    terminals' :: Map.Map TSym (Associativity, Precedence)
    terminals' = Map.insert TSEOF (ANone, maxPrec) terminals
    productions' :: Map.Map ProductionRule Precedence
    productions' = Map.insert (start', [NS start, TS TSEOF]) maxPrec productions
    getMarkSym :: LR0Item -> Maybe Sym
    getMarkSym item = case getRIGHT item of
        [] -> Nothing
        sym : syms -> Just sym
    getCannonical0 :: Cannonical0
    getCannonical0 = runIdentity makeCannonical0 where
        getClosure :: Set.Set LR0Item -> Identity (Set.Set LR0Item)
        getClosure items = if items == items' then return items' else getClosure items' where
            items' :: Set.Set LR0Item
            items' = foldr Set.insert items
                [ LR0Item lhs [] rhs
                | ((lhs, rhs), prec) <- Map.toList productions'
                , any (\item -> getMarkSym item == Just (NS lhs)) (Set.toList items)
                ]
        calcGOTO :: (Set.Set LR0Item, Sym) -> Identity (Set.Set LR0Item)
        calcGOTO (items, sym)
            | sym == TS TSEOF = return Set.empty
            | otherwise = getClosure $ Set.fromList
                [ LR0Item lhs (left ++ [sym']) right
                | LR0Item lhs left (sym' : right) <- Set.toList items
                , sym == sym'
                ]
        loop :: Cannonical0 -> Identity Cannonical0
        loop collection = do
            (_, collection') <- flip runStateT collection $ sequence
                [ do
                    cl <- lift (getClosure items)
                    sequence
                        [ do 
                            items' <- lift (calcGOTO (items, sym))
                            if Set.null items'
                                then return () 
                                else do
                                    Cannonical0 vertices root edges <- get
                                    case Map.lookup items' vertices of
                                        Nothing -> do
                                            let p = Map.size vertices
                                            put (Cannonical0 (Map.insert items' p vertices) root (Map.insert (q, sym) p edges))
                                        Just p -> put (Cannonical0 vertices root (Map.insert (q, sym) p edges))
                        | Just sym <- Set.toList (Set.map getMarkSym cl)
                        ]
                | (items, q) <- Map.toList (getVertices collection)
                ]
            if collection == collection'
                then return collection'
                else loop collection'
        makeCannonical0 :: Identity Cannonical0
        makeCannonical0 = do
            items0 <- getClosure (Set.singleton (LR0Item start' [] [NS start, TS TSEOF]))
            loop (Cannonical0 (Map.singleton items0 0) 0 Map.empty)
    getFIRST :: Map.Map NSym TerminalSet
    getFIRST = loop base where
        base :: Map.Map NSym TerminalSet
        base = Map.fromAscList
            [ (lhs, TerminalSet Set.empty)
            | ((lhs, _), _) <- Map.toAscList productions'
            ]
        loop :: Map.Map NSym TerminalSet -> Map.Map NSym TerminalSet
        loop mapping = if mapping == mapping' then mapping' else loop mapping' where
            getFirstOf :: Sym -> TerminalSet
            getFirstOf (NS ns) = fromJust (Map.lookup ns mapping)
            getFirstOf (TS ts) = TerminalSet (Set.singleton (Just ts))
            go :: (NSym, [Sym]) -> TerminalSet -> Maybe TerminalSet
            go (lhs, rhs) tss = Just (TerminalSet (unTerminalSet tss `Set.union` unTerminalSet (mconcat [ getFirstOf sym | sym <- rhs ])))
            mapping' :: Map.Map NSym TerminalSet
            mapping' = foldr (Map.update <$> go <*> fst) mapping (map fst (Map.toList productions'))
    getFollow :: Map.Map NSym TerminalSet
    getFollow = runIdentity makeFollow where
        makeFollow :: Identity (Map.Map NSym TerminalSet)
        makeFollow = do
            (_, m) <- runStateT (mapM_ (loop1 . fst) (Map.toAscList productions') >> whileTrue loop2) (Map.singleton start' (TerminalSet (Set.singleton (Just TSEOF))))
            return m
        loop1 :: ProductionRule -> StateT (Map.Map NSym TerminalSet) Identity ()
        loop1 (lhs, rhs) = do
            sequence_
                [ modify (add ns (TerminalSet $! Nothing `Set.delete` unTerminalSet (getFIRST Map.! ns)))
                | NS ns : beta <- iterate tail rhs
                , beta /= []
                ]
        loop2 :: StateT (Map.Map NSym TerminalSet) Identity (Bool, ())
        loop2 = (flip (,) ()) <$> go False [ (lhs, rhs, suf) | ((lhs, rhs), _) <- Map.toList productions', suf <- iterate tail rhs ] where
            go :: Bool -> [(NSym, [Sym], [Sym])] -> StateT (Map.Map NSym TerminalSet) Identity Bool
            go changed [] = return changed
            go changed ((_A, rhs, suf) : triples)
                | [NS _B] <- suf = do
                    m <- get
                    put (add _B (m Map.! _A) m)
                    go (changed || unTerminalSet (m Map.! _A) `Set.isSubsetOf` unTerminalSet (m Map.! _B)) triples
                | NS _B : _ <- suf, Nothing `Set.member` unTerminalSet (getFIRST Map.! _B) = do
                    m <- get
                    put (add _B (m Map.! _A) m)
                    go (changed || unTerminalSet (m Map.! _A) `Set.isSubsetOf` unTerminalSet (m Map.! _B)) triples
                | otherwise = go changed triples
        add :: (Ord k) => k -> TerminalSet -> Map.Map k TerminalSet -> Map.Map k TerminalSet
        add k tss = Map.alter (Just . maybe tss (TerminalSet . Set.union (unTerminalSet tss) . unTerminalSet)) k
        whileTrue :: Monad m => m (Bool, a) -> m a
        whileTrue m = do
            (b, x) <- m
            if b then whileTrue m else return x
    getLATable :: [((ParserS, TSym), ProductionRule)]
    getLATable = runIdentity makeLATable where
        calcGOTO' :: ParserS -> [Sym] -> Maybe ParserS
        calcGOTO' q [] = return q
        calcGOTO' q (sym : syms) = do
            q' <- (q, sym) `Map.lookup` getEdges getCannonical0
            calcGOTO' q' syms
        getFirstOf :: [Sym] -> TerminalSet
        getFirstOf [] = mempty
        getFirstOf (NS ns : syms) = case Map.lookup ns getFIRST of
            Nothing -> error "getLALR1.getLATable.getFirstOf"
            Just tss -> tss <> getFirstOf syms
        getFirstOf (TS ts : _) = TerminalSet (Set.singleton (Just ts))
        getLA :: Map.Map (ParserS, LR0Item) TerminalSet -> (ParserS, LR0Item) -> TerminalSet
        getLA m (p, LR0Item lhs left right)
            | lhs == start' = TerminalSet $ Set.singleton (Just TSEOF)
            | otherwise = TerminalSet $ unTerminalSet (la (p, LR0Item lhs left right)) `Set.union` Set.unions [ unTerminalSet $! getFirstOf right' <> la (q, LR0Item lhs' left' (sym' : right')) | (items', q) <- Map.toList (getVertices getCannonical0), calcGOTO' q left == Just p, LR0Item lhs' left' (sym' : right') <- Set.toList items', sym' == NS lhs ]
            where
                la :: (ParserS, LR0Item) -> TerminalSet
                la (q, item) = fromMaybe mempty $ (q, item) `Map.lookup` m
        lfp :: Map.Map (ParserS, LR0Item) TerminalSet
        lfp = go (Map.singleton (getRoot getCannonical0, LR0Item start' [] [NS start, TS TSEOF]) (TerminalSet (Set.singleton (Just TSEOF)))) where
            go :: Map.Map (ParserS, LR0Item) TerminalSet -> Map.Map (ParserS, LR0Item) TerminalSet
            go m = if m == m' then m' else go m' where
                m' :: Map.Map (ParserS, LR0Item) TerminalSet
                m' = Map.fromList [ ((q, item), getLA m (q, item)) | (items, q) <- Map.toList (getVertices getCannonical0), item <- Set.toList items ]
        makeLATable :: Identity [((ParserS, TSym), ProductionRule)]
        makeLATable = do
            triples <- sequence [ return ((q, item), lfp Map.! (q, item)) | (items, q) <- Map.toList (getVertices getCannonical0), item <- Set.toList items, getMarkSym item `elem` [Nothing, Just (TS TSEOF)] ]
            return [ ((q, t), (lhs, left ++ right)) | ((q, LR0Item lhs left right), ts) <- triples, Just t <- Set.toList (unTerminalSet ts) ]
    getLATable' :: [((ParserS, TSym), ProductionRule)]
    getLATable' = [ ((q, t), (lhs, rhs)) | ((q, (lhs, rhs)), ts) <- Map.toList _LA, t <- Set.toList ts ] where
        delta' :: ParserS -> [Sym] -> Maybe ParserS
        delta' q [] = return q
        delta' q (sym : syms) = do
            q' <- (q, sym) `Map.lookup` getEdges getCannonical0
            delta' q' syms
        getFirstOf :: [Sym] -> TerminalSet
        getFirstOf [] = mempty
        getFirstOf (TS ts : _) = TerminalSet (Set.singleton (Just ts))
        getFirstOf (NS ns : syms) = case Map.lookup ns getFIRST of
            Nothing -> error "getLALR1.getLATable.getFirstOf"
            Just tss -> tss <> getFirstOf syms
        _Read :: Map.Map (ParserS, NSym) (Set.Set TSym)
        _Read = Map.fromList
            [ ((p, _A), Set.fromList [ t | Just t <- Set.toList $ unTerminalSet (getFirstOf alpha2) ])
            | (items, p) <- Map.toList (getVertices getCannonical0)
            , LR0Item _B alpha1 (NS _A : alpha2) <- Set.toList items
            ]
        _Follow :: Map.Map (ParserS, NSym) (Set.Set TSym)
        _Follow = digraph my_X my_R my_F' where
            my_X :: Set.Set (ParserS, NSym)
            my_X = Set.fromList
                [ (p, _A)
                | (items, p) <- Map.toList (getVertices getCannonical0)
                , LR0Item _B alpha1 (NS _A : alpha2) <- Set.toList items
                ]
            my_F' :: (ParserS, NSym) -> Set.Set TSym
            my_F' (p, _A) = _Read Map.! (p, _A)
            my_R :: (ParserS, NSym) -> (ParserS, NSym) -> Bool
            my_R (p, _A) (q, _B) = or
                [ Nothing `Set.member` unTerminalSet (getFirstOf alpha2) && delta' p alpha1 == Just q
                | (items, p') <- Map.toList (getVertices getCannonical0)
                , p == p'
                , LR0Item _B' alpha1 (NS _A' : alpha2) <- Set.toList items
                , _A == _A'
                ]
        _LA :: Map.Map (ParserS, ProductionRule) (Set.Set TSym)
        _LA = Map.fromList
            [
                ( (q, (getLHS item, getLEFT item ++ getRIGHT item))
                , Set.unions
                    [ _Follow Map.! (p, _A)
                    | (items', p) <- Map.toList (getVertices getCannonical0)
                    , LR0Item _B alpha1 (NS _A : alpha2) <- Set.toList items'
                    , getLHS item == _A
                    , delta' p (getLEFT item) == Just q
                    ]
                )
            | (items, q) <- Map.toList (getVertices getCannonical0)
            , item <- Set.toList items
            , getMarkSym item `elem` [Nothing, Just (TS TSEOF)]
            ]
    resolveConflicts :: Either Conflict (Map.Map (ParserS, TSym) Action)
    resolveConflicts = foldr loop (Right base) getLATable' where
        base :: Map.Map (ParserS, TSym) Action
        base = Map.fromList
            [ ((q, t), Shift p)
            | ((q, TS t), p) <- Map.toList (getEdges getCannonical0)
            ]
        loop :: ((ParserS, TSym), ProductionRule) -> Either Conflict (Map.Map (ParserS, TSym) Action) -> Either Conflict (Map.Map (ParserS, TSym) Action)
        loop _ (Left str) = Left str
        loop ((q, t), production) (Right getActionT) = case (Map.lookup (q, t) getActionT, if fst production == start' then Accept else Reduce production) of
            (Nothing, ra) -> Right (Map.insert (q, t) ra getActionT)
            (Just Accept, ra) -> Right getActionT
            (Just (Shift p), ra) -> case (Map.lookup t terminals', Map.lookup production productions') of
                (Just (assoc, prec1), Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                    | assoc == ALeft -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                    | assoc == ARight -> Right getActionT
                _ -> Left (Conflict { because = (Shift p, ra), whereIs = (q, t), withEnv = getCannonical0 })
            (Just (Reduce production'), ra) -> case (Map.lookup production' productions', Map.lookup production productions') of
                (Just prec1, Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.update (const (Just ra)) (q, t) getActionT)
                _ -> Left (Conflict { because = (Reduce production', ra), whereIs = (q, t), withEnv = getCannonical0 })
    theResult :: ExceptT Conflict Identity (Cannonical0, LR1Parser)
    theResult = case resolveConflicts of
        Left conflict -> throwE conflict
        Right getActionT -> return 
            ( getCannonical0
            , LR1Parser
                { getInitialS = getRoot getCannonical0
                , getActionTable = getActionT
                , getReduceTable = Map.fromList
                    [ ((q, nt), p)
                    | ((q, NS nt), p) <- Map.toList (getEdges getCannonical0)
                    ]
                }
            )
