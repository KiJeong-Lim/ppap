module PGS.Make where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import PGS.Util
import Y.Base
import Z.Algo.Function
import Z.Algo.Sorting
import Z.Utils
import Data.Maybe (isJust, isNothing)

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
                (q, items) <- sortByMerging (\pair1 -> \pair2 -> snd pair1 < snd pair2) (Map.toAscList vertices)
                return (q, Set.toAscList items)
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

makeCollectionAndLALR1Parser :: CFGrammar -> ExceptT Conflict Identity ((Cannonical0, (Map.Map NSym TerminalSet, [((ParserS, ProductionRule), Set.Set TSym)])), LR1Parser)
makeCollectionAndLALR1Parser (CFGrammar start terminals productions) = theResult where
    maxPrec :: Precedence
    maxPrec = 100
    start' :: NSym
    start' = NSVar "\\ACCEPT"
    terminals' :: Map.Map TSym (Associativity, Precedence)
    terminals' = Map.insert TSEOF (ANone, maxPrec) terminals
    productions' :: Map.Map ProductionRule Precedence
    productions' = Map.insert (start', [NS start]) maxPrec productions
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
                                    case [ _p | (_p, _item') <- Map.toAscList vertices, items' == _item' ] of
                                        [] -> do
                                            let p = Map.size vertices
                                            put (Cannonical0 (Map.insert p items' vertices) root (Map.insert (q, sym) p edges))
                                        [p] -> put (Cannonical0 vertices root (Map.insert (q, sym) p edges))
                                        _ -> error "makeCollectionAndLALR1Parser.getCannonical0.loop"
                        | Just sym <- Set.toList (Set.map getMarkSym cl)
                        ]
                | (q, items) <- Map.toList (getVertices collection)
                ]
            if collection == collection'
                then return collection'
                else loop collection'
        makeCannonical0 :: Identity Cannonical0
        makeCannonical0 = do
            items0 <- getClosure (Set.singleton (LR0Item start' [] [NS start]))
            loop (Cannonical0 (Map.singleton 0 items0) 0 Map.empty)
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
    getLATable :: [((ParserS, ProductionRule), Set.Set TSym)]
    getLATable = runIdentity makeLATable where
        calcGOTO' :: ParserS -> [Sym] -> Maybe ParserS
        calcGOTO' q [] = Just q
        calcGOTO' q (sym : syms) = maybe Nothing (\p -> calcGOTO' p syms) $ Map.lookup (q, sym) (getEdges getCannonical0)
        getFirstOf :: [Sym] -> TerminalSet
        getFirstOf [] = mempty
        getFirstOf (NS ns : syms) = case Map.lookup ns getFIRST of
            Nothing -> error "getLALR1.getLATable.getFirstOf"
            Just tss -> tss <> getFirstOf syms
        getFirstOf (TS ts : _) = TerminalSet (Set.singleton (Just ts))
        getLA :: Int -> (ParserS, LR0Item) -> StateT (Map.Map (ParserS, LR0Item) (Int, TerminalSet)) Identity (Int, TerminalSet)
        getLA k (q, item)
            | getLHS item == start' = return (0, TerminalSet (Set.singleton (Just TSEOF)))
            | otherwise = do
                m <- get
                case (q, item) `Map.lookup` m of
                    Just (k0, TerminalSet tss)
                        | k >= k0 -> return (k0, TerminalSet tss)
                    _ -> do
                        put (Map.insert (q, item) (k, TerminalSet Set.empty) m)
                        result <- fmap (TerminalSet . Set.unions) $ sequence
                            [ fmap Set.unions $ sequence
                                [ do
                                    let tss = unTerminalSet (getFirstOf (tail (getRIGHT item')))
                                    if Nothing `Set.member` tss then do
                                        (k0, result) <- getLA (k + 1) (q', item')
                                        return ((Nothing `Set.delete` tss) `Set.union` unTerminalSet result)
                                    else return tss
                                | item' <- Set.toAscList items'
                                , getMarkSym item' == Just (NS (getLHS item))
                                ]
                            | (q', items') <- Map.toAscList (getVertices getCannonical0)
                            , calcGOTO' q' (getLEFT item) == Just q
                            ]
                        modify (Map.update (const (Just (0, result))) (q, item))
                        return (0, result)
        makeLATable :: Identity [((ParserS, ProductionRule), Set.Set TSym)]
        makeLATable = do
            (triples, _) <- flip runStateT Map.empty $ sequence
                [ do
                    (_, result) <- getLA 1 (q, item)
                    return ((q, (getLHS item, getLEFT item)), Set.fromAscList [ t | Just t <- Set.toAscList (unTerminalSet result) ])
                | (q, items) <- Map.toAscList (getVertices getCannonical0)
                , item <- Set.toAscList items
                , isNothing (getMarkSym item)
                ]
            return triples
    resolveConflicts :: Either Conflict (Map.Map (ParserS, TSym) Action)
    resolveConflicts = foldr loop (Right base) [ ((q, t), (lhs, rhs)) | ((q, (lhs, rhs)), ts) <- getLATable, t <- Set.toList ts ] where
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
    theResult :: ExceptT Conflict Identity ((Cannonical0, (Map.Map NSym TerminalSet, [((ParserS, ProductionRule), Set.Set TSym)])), LR1Parser)
    theResult = case resolveConflicts of
        Left conflict -> throwE conflict
        Right getActionT -> return 
            ( (getCannonical0, (getFIRST, getLATable))
            , LR1Parser
                { getInitialS = getRoot getCannonical0
                , getActionTable = getActionT
                , getReduceTable = Map.fromList
                    [ ((q, nt), p)
                    | ((q, NS nt), p) <- Map.toList (getEdges getCannonical0)
                    ]
                }
            )
