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
                (q, items) <- Map.toAscList vertices
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
    productions' = Map.insert (start', [NS start, TS TSEOF]) maxPrec productions
    getMarkSym :: LR0Item -> Maybe Sym
    getMarkSym (LR0Item _ _ []) = Nothing
    getMarkSym (LR0Item _ _ (sym : _)) = Just sym
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
        calcGOTO (items, sym) = getClosure $ Set.fromList
            [ LR0Item lhs (left ++ [sym']) right
            | LR0Item lhs left (sym' : right) <- Set.toList items
            , sym == sym'
            ]
        loop :: Cannonical0 -> Identity Cannonical0
        loop collection = do
            (_, collection') <- flip runStateT collection $ sequence_
                [ do
                    cl <- lift (getClosure items)
                    sequence_
                        [ do 
                            items' <- lift (calcGOTO (items, sym))
                            if Set.null items' then
                                return () 
                            else do
                                Cannonical0 vertices root edges <- get
                                let ps = [ _p | (_p, _items') <- Map.toAscList vertices, items' == _items' ]
                                case ps of
                                    [] -> do
                                        let p = Map.size vertices
                                        put (Cannonical0 (Map.insert p items' vertices) root (Map.insert (q, sym) p edges))
                                    [p] -> put (Cannonical0 vertices root (Map.insert (q, sym) p edges))
                                    _ -> error "makeCollectionAndLALR1Parser.getCannonical0.loop"
                        | Just sym <- Set.toList (Set.map getMarkSym cl)
                        ]
                | (q, items) <- Map.toList (getVertices collection)
                ]
            if collection == collection' then return collection' else loop collection'
        makeCannonical0 :: Identity Cannonical0
        makeCannonical0 = do
            items0 <- getClosure (Set.singleton (LR0Item start' [] [NS start, TS TSEOF]))
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
        calcGOTO :: ParserS -> [Sym] -> Maybe ParserS
        calcGOTO q [] = return q
        calcGOTO q (sym : syms) = do
            p <- Map.lookup (q, sym) (getEdges getCannonical0)
            calcGOTO p syms
        getFirstOf :: [Sym] -> TerminalSet
        getFirstOf [] = mempty
        getFirstOf (NS ns : syms) = getFIRST Map.! ns <> getFirstOf syms
        getFirstOf (TS ts : _) = TerminalSet (Set.singleton (Just ts))
        isNullable :: [Sym] -> Bool
        isNullable omega = Nothing `Set.member` unTerminalSet (getFirstOf omega)
        _Domain :: Set.Set (ParserS, NSym)
        _Domain = Set.fromList [ (p, _A) | (p, items') <- Map.toAscList (getVertices getCannonical0), LR0Item _ _ (NS _A : _) <- Set.toAscList items' ]
        _Read :: Map.Map (ParserS, NSym) (Set.Set TSym)
        _Read = digraph _Domain _reads _DR where
            _reads (p, _A) (r, _C) = calcGOTO p [NS _A] == Just r && isNullable [NS _C]
            _DR (p, _A) = Set.fromList [ t | t <- Set.toAscList (Map.keysSet terminals'), isJust (calcGOTO p [NS _A, TS t]) ]
        _Follow :: Map.Map (ParserS, NSym) (Set.Set TSym)
        _Follow = digraph _Domain _includes (call _Read) where
            _includes (p, _A) (p', _B) = or
                [ calcGOTO p' _beta == Just p && isNullable _gamma
                | LR0Item _B' _beta (NS _A' : _gamma) <- Set.toAscList (getVertices getCannonical0 Map.! p)
                , _A == _A' && _B == _B'
                ]
        makeLATable :: Identity [((ParserS, ProductionRule), Set.Set TSym)]
        makeLATable = sequence
            [ do
                result <- sequence
                    [ return (_Follow Map.! (p, _A))
                    | (p, items') <- Map.toAscList (getVertices getCannonical0)
                    , calcGOTO p _omega == Just q
                    , isJust (calcGOTO p [NS _A])
                    ]
                return ((q, (_A, _omega)), Set.unions result)
            | (q, items) <- Map.toAscList (getVertices getCannonical0)
            , LR0Item _A _omega [] <- Set.toAscList items
            ]
    resolveConflicts :: Either Conflict (Map.Map (ParserS, TSym) Action)
    resolveConflicts = foldr loop (Right base) [ ((q, t), (lhs, rhs)) | ((q, (lhs, rhs)), ts) <- getLATable, t <- Set.toList ts ] where
        base :: Map.Map (ParserS, TSym) Action
        base = Map.fromList
            [ ((q, t), if t == TSEOF then Accept else Shift p)
            | ((q, TS t), p) <- Map.toList (getEdges getCannonical0)
            ]
        loop :: ((ParserS, TSym), ProductionRule) -> Either Conflict (Map.Map (ParserS, TSym) Action) -> Either Conflict (Map.Map (ParserS, TSym) Action)
        loop _ (Left conf) = Left conf
        loop ((q, t), production) (Right getActionT) = case (Map.lookup (q, t) getActionT, Reduce production) of
            (Nothing, ra) -> Right (Map.insert (q, t) ra getActionT)
            (Just Accept, ra) -> Right getActionT
            (Just (Shift p), ra) -> case (Map.lookup t terminals', Map.lookup production productions') of
                (Just (assoc, prec1), Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.adjust (const ra) (q, t) getActionT)
                    | assoc == ALeft -> Right (Map.adjust (const ra) (q, t) getActionT)
                    | assoc == ARight -> Right getActionT
                _ -> Left (Conflict { because = (Shift p, ra), whereIs = (q, t), withEnv = getCannonical0 })
            (Just (Reduce production'), ra) -> case (Map.lookup production' productions', Map.lookup production productions') of
                (Just prec1, Just prec2)
                    | prec1 > prec2 -> Right getActionT
                    | prec1 < prec2 -> Right (Map.adjust (const ra) (q, t) getActionT)
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
