module PGS.Alpha1 where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Foldable
import Data.Functor hiding (unzip)
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (isJust, isNothing)
import qualified Z.PC as P
import Z.Algorithms
import Z.System
import Z.Utils

type ProductionRule = (NSym, [Sym])

type ParserS = Int

type HsCode = [String]

data Associativity
    = ALeft
    | ARight
    | ANone
    deriving (Eq, Show)

data NSym
    = NSVar String
    | NSApp NSym NSym
    deriving (Eq, Ord, Show)

data TSym
    = TSEOF
    | TSVar String
    deriving (Eq, Ord, Show)

data Sym
    = NS NSym
    | TS TSym
    deriving (Eq, Ord, Show)

data CFGrammar
    = CFGrammar
        { getStartSym :: NSym
        , getTerminalSyms :: Map.Map TSym (Associativity, Precedence)
        , getProductionRules :: Map.Map ProductionRule Precedence
        }
    deriving (Eq)

data LR0Item
    = LR0Item
        { getLHS :: NSym
        , getLEFT :: [Sym]
        , getRIGHT :: [Sym]
        }
    deriving (Eq, Ord)

data Cannonical0
    = Cannonical0
        { getVertices :: Map.Map ParserS (Set.Set LR0Item)
        , getRoot :: ParserS
        , getEdges :: Map.Map (ParserS, Sym) ParserS
        }
    deriving (Eq)

data Action
    = Shift ParserS
    | Reduce ProductionRule
    | Accept
    deriving (Eq, Show)

data LR1Parser
    = LR1Parser
        { getInitialS :: ParserS
        , getActionTable :: Map.Map (ParserS, TSym) Action
        , getReduceTable :: Map.Map (ParserS, NSym) ParserS
        }
    deriving (Eq)

newtype TerminalSet
    = TerminalSet { unTerminalSet :: Set.Set (Maybe TSym) }
    deriving (Eq)

data Destructor
    = DsStrLit String
    | DsSource String
    | DsNSPatn Int
    | DsTSPatn Int String
    deriving (Show)

data YMatch
    = YMatch
        { getMatchingPrec :: Precedence
        , getMatchingPats :: [Sym]
        , getDestructorss :: [[Destructor]]
        }
    deriving (Show)

data Scheme
    = Scheme
        { getTypeConstr :: Maybe String
        , getSchemeDecl :: (String, String)
        , getParamsDecl :: [(String, String)]
        , getMatchDecls :: [YMatch]
        }
    deriving (Show)

data TerminalInfo
    = TerminalInfo
        { getTerminalPatn :: String
        , getTerminalName :: TSym
        , getTerminalPrec :: Precedence
        , getTerminalAsso :: Associativity
        }
    deriving (Show)

data YTarget
    = YTarget
        { getTokenType :: String
        , getParserName :: String
        , getResultType :: String
        , getStartSymbol :: NSym
        , getTerminalInfos :: [TerminalInfo]
        }
    deriving (Show)

data YBlock
    = HsHead HsCode
    | HsTail HsCode
    | Define Scheme
    | Target YTarget
    deriving (Show)

data Conflict
    = Conflict
        { because :: (Action, Action)
        , whereIs :: (ParserS, TSym)
        , withEnv :: Cannonical0
        }
    deriving ()

readTSym :: P.P TSym
readTSym = mconcat
    [ P.consume "\\$" $> TSEOF
    , P.consume "$" *> (TSVar <$> P.smallid)
    ]

readNSym :: P.P NSym
readNSym = go 0 where
    go :: Int -> P.P NSym
    go 0 = List.foldl' NSApp <$> go 1 <*> many (P.consume " " *> go 1)
    go 1 = mconcat
        [ P.consume "$" *> (NSVar <$> P.largeid)
        , go 2
        ]
    go _ = P.consume "(" *> go 0 <* P.consume ")"

readDestructors :: P.P [Destructor]
readDestructors
    = mconcat
        [ do
            de <- DsSource <$> P.regex "[.\\'\\n'\\'$'\\'\\\"']+"
            des <- readDestructors
            return (de : des)
        , do
            de <- DsStrLit <$> P.quote
            des <- readDestructors
            return (de : des)
        , do
            P.consume "$"
            P.neg (P.accept (\ch -> ch == ' '))
            idx <- P.int
            de <- mconcat
                [ do
                    P.consume "."
                    field <- P.regex "['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*"
                    return (DsTSPatn idx field)
                , P.neg (P.consume ".") $> DsNSPatn idx
                ]
            des <- readDestructors
            return (de : des)
        , do
            P.consume "$"
            str <- many (P.accept (\ch -> ch == ' '))
            when (null str) $ P.neg P.int
            des <- readDestructors
            return (DsSource ("$" ++ str) : des)
        , P.lend $> []
        ]

readSym :: P.P Sym
readSym = mconcat
    [ NS <$> readNSym
    , TS <$> readTSym
    ]

readYMatch :: P.P YMatch
readYMatch = do
    P.indent 4
    prec <- P.int
    P.white
    pats <- P.list readSym
    P.consume ":"
    P.lend
    dess <- many (P.indent 8 *> readDestructors)
    return $ YMatch
        { getMatchingPrec = prec
        , getMatchingPats = pats
        , getDestructorss = dess
        }

readScheme :: P.P Scheme
readScheme = do
    P.consume "\\define"
    type_constraint <- mconcat
        [ do
            type_ctx <- P.quote
            P.white
            P.consume "=>"
            return (Just type_ctx)
        , pure Nothing
        ]
    P.white
    P.consume "$"
    body_name <- P.largeid
    params_decl <- many $ do
        P.white
        P.consume "("
        P.consume "$"
        param_name <- P.largeid
        P.white
        P.consume ":"
        P.white
        param_type <- P.quote
        P.consume ")"
        return (param_name, param_type)
    P.white
    P.consume ":"
    P.white
    body_type <- P.quote
    P.white
    P.consume "{"
    P.lend
    matches <- many readYMatch
    P.consume "}"
    P.lend
    return $ Scheme
        { getTypeConstr = type_constraint
        , getSchemeDecl = (body_name, body_type)
        , getParamsDecl = params_decl
        , getMatchDecls = matches
        }

readAssoc :: P.P Associativity
readAssoc = mconcat
    [ P.consume "none" $> ANone
    , P.consume "left" $> ALeft
    , P.consume "right" $> ARight
    ]

readTerminalInfo :: P.P TerminalInfo
readTerminalInfo = do
    P.indent 8
    patn <- P.quote
    P.consume ":"
    P.white
    name <- readTSym
    P.white
    prec <- P.int
    P.white
    assoc <- readAssoc
    P.lend
    return $ TerminalInfo
        { getTerminalPatn = patn
        , getTerminalName = name
        , getTerminalPrec = prec
        , getTerminalAsso = assoc
        }

readTarget :: P.P YTarget
readTarget = do
    P.consume "\\target"
    P.white
    P.consume "{"
    P.lend
    P.indent 4
    P.consume "token-type:"
    P.white
    token_type <- P.quote
    P.lend
    P.indent 4
    P.consume "parser-name:"
    P.white
    parser_name <- P.quote
    P.lend
    P.indent 4
    P.consume "result-type:"
    P.white
    result_type <- P.quote
    P.lend
    P.indent 4
    P.consume "start:"
    P.white
    start <- readNSym
    P.lend
    P.indent 4
    P.consume "terminals:"
    P.lend
    terminal_infos <- many readTerminalInfo
    P.consume "}"
    P.lend
    return $ YTarget
        { getTokenType = token_type
        , getParserName = parser_name
        , getResultType = result_type
        , getStartSymbol = start
        , getTerminalInfos = terminal_infos
        }

readBlock :: P.P YBlock
readBlock = mconcat
    [ do
        P.consume "\\hshead"
        P.white
        P.consume "{"
        P.lend
        hshead <- many ((P.indent 4 *> P.regex "[.\\'\\n']*" <* P.lend) <|> (P.lend $> ""))
        P.consume "}"
        P.lend
        return (HsHead hshead)
    , do
        P.consume "\\hstail"
        P.white
        P.consume "{"
        P.lend
        hstail <- many ((P.indent 4 *> P.regex "[.\\'\\n']*" <* P.lend) <|> (P.lend $> ""))
        P.consume "}"
        P.lend
        return (HsTail hstail)
    , Define <$> readScheme
    , Target <$> readTarget
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
        call :: Map.Map (ParserS, NSym) (Set.Set TSym) -> (ParserS, NSym) -> Set.Set TSym
        call _R _x = _R Map.! _x
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

unFoldNSApp :: NSym -> (String, [NSym])
unFoldNSApp = flip loop [] where
    loop :: NSym -> [NSym] -> (String, [NSym])
    loop (NSVar nsv) nss = (nsv, nss)
    loop (NSApp ns1 ns2) nss = loop ns1 (ns2 : nss)

substituteNS :: [(String, NSym)] -> NSym -> NSym
substituteNS mapsto = loop where
    loop :: NSym -> NSym
    loop (NSVar nsv) = case lookup nsv mapsto of
        Nothing -> NSVar nsv
        Just ns -> ns
    loop (NSApp ns1 ns2) = NSApp (loop ns1) (loop ns2)

makeProductionRuleInstances :: Map.Map String ([String], [YMatch]) -> NSym -> StateT ((Int, Map.Map NSym Int), Map.Map NSym (Maybe [([Sym], Precedence)])) (ExceptT ErrMsg Identity) ()
makeProductionRuleInstances rule_env = fmap (const ()) . loop where
    loop :: NSym -> StateT ((Int, Map.Map NSym Int), Map.Map NSym (Maybe [([Sym], Precedence)])) (ExceptT ErrMsg Identity) NSym
    loop ns = do
        ((max_id_num, id_env), cache) <- get
        case unFoldNSApp ns of
            (nsv, nss) -> case Map.lookup nsv rule_env of
                Nothing -> lift (throwE ("cannot find the defintion of the scheme ``" ++ nsv ++ "\'\'."))
                Just (params, match_decls)
                    | length params /= length nss -> lift (throwE ("args do not match to params: length " ++ showList nss (" /= length " ++ showList params ".")))
                    | otherwise -> do
                        let mapsto = zip params nss
                        case Map.lookup ns id_env of
                            Nothing -> do
                                put ((max_id_num + 1, Map.insert ns max_id_num id_env), Map.insert ns Nothing cache)
                                mapM_ loop nss
                                pairs <- sequence
                                    [ do
                                        pats' <- forM pats $ \pat -> case pat of
                                            NS ns' -> NS <$> loop (substituteNS mapsto ns')
                                            _ -> return pat
                                        return (pats', prec)
                                    | YMatch prec pats destructors <- match_decls
                                    ]
                                (pair', cache') <- get
                                put (pair', Map.update (const (Just (Just pairs))) ns cache')
                            _ -> return ()
                        return (substituteNS mapsto ns)

genParser :: [YBlock] -> ExceptT ErrMsg Identity [String]
genParser blocks = myMain where
    tellLine :: (String -> String) -> WriterT [String] (ExceptT String Identity) ()
    tellLine string_stream = tell [string_stream "\n"]
    getYTarget :: ExceptT ErrMsg Identity YTarget
    getYTarget = case [ y_target | Target y_target <- blocks ] of
        [] -> throwE "a target block required."
        [y_target] -> return y_target
        _ -> throwE "ambiguous target blocks."
    getHsHead :: ExceptT ErrMsg Identity HsCode
    getHsHead = case [ hshead | HsHead hshead <- blocks ] of
        [] -> throwE "a hshead block required."
        [hshead] -> return hshead
        _ -> throwE "ambiguous hshead block."
    getHsTail :: ExceptT ErrMsg Identity HsCode
    getHsTail = case [ hstail | HsTail hstail <- blocks ] of
        [] -> throwE "a hstail block required."
        [hstail] -> return hstail
        _ -> throwE "ambiguous hstail block."
    checkTerminalOccurence :: Set.Set TSym -> Set.Set TSym -> ExceptT ErrMsg Identity ()
    checkTerminalOccurence subs supers
        | subs `Set.isSubsetOf` supers = return ()
        | otherwise = throwE ("definitions of the following terminal symbols required: " ++ concat [ "  " ++ pprint 0 ts "\n" | ts <- Set.toList (subs `Set.difference` supers) ])
    getGetRep :: NSym -> String -> String
    getGetRep = go 0 where
        go :: Int -> NSym -> String -> String
        go 0 (NSApp ns1 ns2) = go 0 ns1 . strstr " " . go 1 ns2
        go 0 ns = go 1 ns
        go 1 (NSVar nsv) = strstr "get" . strstr nsv
        go 1 ns = go 2 ns
        go _ ns = strstr "(" . go 0 ns . strstr ")"
    patTsIdx :: Int -> String -> String -> String
    patTsIdx idx field = strstr field . strstr "_" . shows idx
    patNsIdx :: Int -> String -> String
    patNsIdx idx = strstr "_" . shows idx
    makeNSPatn :: Int -> String -> String
    makeNSPatn idx = strcat
        [ patNsIdx idx
        , strstr "@(PTBranch "
        , guardIdx idx
        , strstr " _)"
        ]
    makeTSPatn :: Map.Map TSym String -> Int -> TSym -> String -> String
    makeTSPatn mapTSymToPatn = loop where
        acceptSmallId :: P.P String
        acceptSmallId = P.regex "['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*"
        makePatn :: Int -> P.P (String -> String)
        makePatn idx = fmap strcat $ many $ mconcat
            [ do
                field <- acceptSmallId
                return (patTsIdx idx field)
            , do
                quote <- P.quote
                return (shows quote)
            , do
                P.neg (acceptSmallId <|> P.quote)
                hs_src <- some (P.accept (\ch -> ch /= ' '))
                return (strstr hs_src)
            , do
                ch <- P.accept (\ch -> ch == ' ')
                return (strstr [ch])
            ]
        loop :: Int -> TSym -> String -> String
        loop idx tsym = case Map.lookup tsym mapTSymToPatn of
            Nothing -> error "`makeTSPatn\'"
            Just patn -> strstr "PTLeaf (" . either (error "`makeTSPatn\'") id (P.execPC (makePatn idx) (P.addLoc patn)) . strstr ")"
    guardIdx :: Int -> String -> String
    guardIdx idx = strstr "guard" . shows idx
    makeGuard :: Map.Map NSym Int -> String -> [String] -> [(Int, Sym)] -> String -> String
    makeGuard id_env body_name params_name zipped_sym
        | null [ (idx, ns) | (idx, NS ns) <- zipped_sym ] = strstr "otherwise"
        | otherwise = guard
        where
            guard :: String -> String
            guard = strcat
                [ strstr "["
                , ppunc ", " [ guardIdx idx | (idx, NS ns) <- zipped_sym ]
                , strstr "] `elem` ["
                , ppunc ", "
                    [ strcat
                        [ strstr "["
                        , ppunc ", "
                            [ case Map.lookup (substituteNS (zip params_name (snd (unFoldNSApp ns1))) ns) id_env of
                                Nothing -> error "makeGuard"
                                Just num -> shows num
                            | (idx, NS ns) <- zipped_sym
                            ]
                        , strstr "]"
                        ]
                    | (ns1, num1) <- Map.toList id_env
                    , body_name == fst (unFoldNSApp ns1)
                    ]
                , strstr "]"
                ]
    formatTable :: Ord a => [((a, b), c)] -> [(a, [(b, c)])]
    formatTable = mSort (\pair1 -> \pair2 -> fst pair1 <= fst pair2) . loop where
        loop :: Eq a => [((a, b), c)] -> [(a, [(b, c)])]
        loop [] = []
        loop (((x, y), z) : triples) = case List.partition (\triple -> fst (fst triple) == x) triples of
            (triples1, triples2) -> (x, (y, z) : [ (y, z) | ((_, y), z) <- triples1 ]) : loop triples2
    getRuleEnv :: [Scheme] -> ExceptT ErrMsg Identity (Map.Map String ([String], [YMatch]))
    getRuleEnv schema = foldrM go Map.empty rules where
        rules :: [(String, ([String], [YMatch]))]
        rules = do
            Scheme type_constraint body params match_decls <- schema
            case (fst body, fst (unzip params)) of
                (body_name, params_name) -> return (body_name, (params_name, match_decls))
        go :: (String, ([String], [YMatch])) -> Map.Map String ([String], [YMatch]) -> ExceptT ErrMsg Identity (Map.Map String ([String], [YMatch]))
        go (body_name, (param_name, match_decls)) rule_env
            = case Map.lookup body_name rule_env of
                Nothing -> return (Map.insert body_name (param_name, match_decls) rule_env)
                _ -> throwE (body_name ++ " has duplicate definitions.")
    myMain :: ExceptT ErrMsg Identity [String]
    myMain = do
        hs_head <- getHsHead
        hs_tail <- getHsTail
        y_target <- getYTarget
        rule_env <- getRuleEnv [ scheme | Define scheme <- blocks ]
        let token_type = getTokenType y_target
            parser_name = getParserName y_target
            result_type = getResultType y_target
            start_symbol = getStartSymbol y_target
            terminal_infos = getTerminalInfos y_target
            rule_env = Map.fromList
                [ case (fst body, fst (unzip params)) of
                    (body_name, params_name) -> (body_name, (params_name, match_decls))
                | Define (Scheme type_constraint body params match_decls) <- blocks
                ]
        ((), ((max_id_num, id_env), cache)) <- runStateT (makeProductionRuleInstances rule_env start_symbol) ((1, Map.empty), Map.empty)
        let cache' = Map.toList cache
            production_rules = Map.fromList
                [ ((lhs, rhs), prec)
                | (lhs, Just pairs) <- cache'
                , (rhs, prec) <- pairs
                ]
            terminal_symbols = Map.fromList
                [ (tsym, (assoc, prec))
                | TerminalInfo patn tsym prec assoc <- terminal_infos
                ]
            getTSymId TSEOF = return 0
            getTSymId (TSVar tsv) = case [ n | (n, TerminalInfo patn ts prec assoc) <- zip [1, 2 .. ] terminal_infos, ts == TSVar tsv ] of
                [] -> throwE ("the terminal symbol " ++ pprint 0 (TSVar tsv) " hasn't been declared.")
                [n] -> return n
                _ -> throwE ("the terminal symbol " ++ pprint 0 (TSVar tsv) " has been declared twice or more.")
            getNSymId nsym = maybe (throwE ("the terminal symbol " ++ pprint 0 nsym " hasn't been declared.")) return (Map.lookup nsym id_env)
        checkTerminalOccurence (Set.fromList [ ts | (lhs, Just pairs) <- cache', (rhs, prec) <- pairs, TS ts <- rhs ]) (Set.fromList [ tsym | TerminalInfo patn tsym prec assoc <- terminal_infos ])
        ((collection, (_First, _LA)), lalr1) <- catchE (makeCollectionAndLALR1Parser (CFGrammar { getStartSym = start_symbol, getTerminalSyms = terminal_symbols, getProductionRules = production_rules })) $ throwE . show
        ((), y_out) <- runWriterT $ do
            tellLine (ppunc "\n" (map strstr hs_head))
            tellLine (strstr "import qualified Control.Monad.Trans.Class as Y")
            tellLine (strstr "import qualified Control.Monad.Trans.Except as Y")
            tellLine (strstr "import qualified Control.Monad.Trans.State.Strict as Y")
            tellLine (strstr "import qualified Data.Map.Strict as YMap")
            tellLine (strstr "import qualified Data.Set as YSet")
            tellLine (ppunc "\n" (strstr "" : map strstr hs_tail))
            if null hs_tail then return () else tellLine (strstr "")
            tellLine (strstr "-- the following codes are generated by PGS.")
            tellLine (strstr "")
            tellLine (strstr "type ParserS = Int")
            tellLine (strstr "")
            tellLine (strstr "type NSym = Int")
            tellLine (strstr "")
            tellLine (strstr "type TSym = Int")
            tellLine (strstr "")
            tellLine (strstr "data Sym")
            tellLine (strstr "    = NS NSym")
            tellLine (strstr "    | TS TSym")
            tellLine (strstr "    deriving (Eq, Ord)")
            tellLine (strstr "")
            tellLine (strstr "data Action")
            tellLine (strstr "    = Shift ParserS")
            tellLine (strstr "    | Reduce (NSym, [Sym])")
            tellLine (strstr "    | Accept")
            tellLine (strstr "    deriving (Eq)")
            tellLine (strstr "")
            tellLine (strstr "data LR1Parser")
            tellLine (strstr "    = LR1Parser")
            tellLine (strstr "        { getInitialS :: ParserS")
            tellLine (strstr "        , getActionTable :: YMap.Map (ParserS, TSym) Action")
            tellLine (strstr "        , getReduceTable :: YMap.Map (ParserS, NSym) ParserS")
            tellLine (strstr "        }")
            tellLine (strstr "    deriving ()")
            tellLine (strstr "")
            tellLine (strstr "data ParsingTree")
            tellLine (strstr "    = PTLeaf (" . strstr token_type . strstr ")")
            tellLine (strstr "    | PTBranch NSym [ParsingTree]")
            tellLine (strstr "    deriving ()")
            tellLine (strstr "")
            tellLine (strstr parser_name . strstr " :: [" . strstr token_type . strstr "] -> Either (Maybe (" . strstr token_type . strstr ")) (" . strstr result_type . strstr ")")
            tellLine (strstr parser_name . strstr " = fmap (" . getGetRep start_symbol . strstr ") . runLALR1 theLALR1Parser where")
            sequence
                [ do
                    let body_name = fst body
                        body_type = snd body
                        params_name = fst (unzip params)
                        params_type = snd (unzip params)
                    tellLine $ strcat
                        [ strstr "    get"
                        , strstr body_name
                        , strstr " :: "
                        , strstr (maybe "" (\type_ctx -> type_ctx ++ " => ") type_constraint)
                        , foldr (\arg_typ -> \acc -> strstr "(ParsingTree -> (" . strstr arg_typ . strstr ")) -> " . acc) (strstr "ParsingTree -> (" . strstr body_type . strstr ")") params_type
                        ]
                    sequence
                        [ do
                            tellLine $ strcat
                                [ strstr "    get"
                                , strstr body_name
                                , strcat [ strstr " get" . strstr param_name | param_name <- params_name ]
                                , strstr " (PTBranch _ ["
                                , ppunc ", "
                                    [ case sym of
                                        NS ns -> makeNSPatn idx
                                        TS ts -> makeTSPatn (Map.fromList [ (tsym, patn) | TerminalInfo patn tsym _ _ <- terminal_infos ]) idx ts
                                    | (idx, sym) <- zip [1, 2 .. ] syms
                                    ]
                                , strstr "])"
                                ]
                            sequence
                                [ do
                                    let mkIndexErr idx = "the length of rhs is " ++ shows (length syms) (", but the index " ++ shows idx " is greater than or equal to it.")
                                    des_rep <- fmap (ppunc  "        ") $ sequence
                                        [ lift $ fmap strcat $ sequence
                                            [ case de of
                                                DsStrLit str -> return (shows str)
                                                DsSource hs_src -> return (strstr hs_src)
                                                DsNSPatn idx
                                                    | idx <= length syms -> case syms !! (idx - 1) of
                                                        NS ns -> return (strstr "(" . getGetRep ns . strstr " " . patNsIdx idx . strstr ")")
                                                        TS ts -> throwE ("a DsTSPatn must be matched to a nonterminal symbol.")
                                                    | otherwise -> throwE (mkIndexErr idx)
                                                DsTSPatn idx field
                                                    | idx <= length syms -> case syms !! (idx - 1) of
                                                        NS ns -> throwE ("a DsTSPatn must be matched to a terminal symbol.")
                                                        TS ts -> return (strstr "(" . patTsIdx idx field . strstr ")")
                                                    | otherwise -> throwE (mkIndexErr idx)
                                            | de <- des
                                            ]
                                        ]
                                    tellLine $ strcat
                                        [ strstr "        | "
                                        , makeGuard id_env body_name params_name (zip [1, 2 .. ] syms)
                                        , strstr " = "
                                        , des_rep
                                        ]
                                    return ()
                                | des <- dess
                                ]
                            return ()
                        | YMatch prec syms dess <- match_decls
                        ]
                    return ()
                | Define (Scheme type_constraint body params match_decls) <- blocks
                ]
            tellLine (strstr "    toTerminal :: (" . strstr token_type . strstr ") -> TSym")
            sequence
                [ do
                    tsym_id <- lift (getTSymId tsym)
                    tellLine (strstr "    toTerminal (" . strstr patn . strstr ") = " . shows tsym_id)
                | TerminalInfo patn tsym prec assoc <- terminal_infos
                ]
            tellLine (strstr "    runLALR1 :: LR1Parser -> [" . strstr token_type . strstr "] -> Either (Maybe (" . strstr token_type . strstr ")) ParsingTree")
            tellLine (strstr "    runLALR1 (LR1Parser getInitS getActionT getReduceT) = go where")
            tellLine (strstr "        loop inputs = do")
            tellLine (strstr "            let cur = if null inputs then 0 else toTerminal (head inputs)")
            tellLine (strstr "                exception = Y.lift (if null inputs then Left Nothing else Left (Just (head inputs)))")
            tellLine (strstr "            (stack, trees) <- Y.get")
            tellLine (strstr "            case YMap.lookup (head stack, cur) getActionT of")
            tellLine (strstr "                Nothing -> exception")
            tellLine (strstr "                Just Accept -> return ()")
            tellLine (strstr "                Just (Shift top') -> do")
            tellLine (strstr "                    Y.put (top' : stack, PTLeaf (head inputs) : trees)")
            tellLine (strstr "                    loop (tail inputs)")
            tellLine (strstr "                Just (Reduce (lhs, rhs)) -> do")
            tellLine (strstr "                    let n = length rhs")
            tellLine (strstr "                    case YMap.lookup (stack !! n, lhs) getReduceT of")
            tellLine (strstr "                        Nothing -> exception")
            tellLine (strstr "                        Just top' -> do")
            tellLine (strstr "                            Y.put (top' : drop n stack, PTBranch lhs (reverse (take n trees)) : drop n trees)")
            tellLine (strstr "                            loop inputs")
            tellLine (strstr "        go tokens = do")
            tellLine (strstr "            (_, (_, result)) <- Y.runStateT (loop tokens) ([getInitS], [])")
            tellLine (strstr "            case result of")
            tellLine (strstr "                [output] -> return output")
            tellLine (strstr "    theLALR1Parser :: LR1Parser")
            tellLine (strstr "    theLALR1Parser = LR1Parser")
            tellLine (strstr "        { getInitialS = " . shows (getInitialS lalr1))
            action_table_rep <- lift $ sequence
                [ fmap (ppunc ", ") $ do
                    pairs' <- sequence
                        [ do
                            tsym_id <- getTSymId tsym
                            return (tsym_id, action)
                        | (tsym, action) <- pairs
                        ]
                    sequence
                        [ case action of
                            Shift p -> return $ strcat
                                [ strstr "(("
                                , shows q
                                , strstr ", "
                                , shows tsym_id
                                , strstr "), Shift "
                                , shows p
                                , strstr ")"
                                ]
                            Reduce (lhs, rhs) -> do
                                lhs_rep <- getNSymId lhs
                                rhs_rep <- sequence
                                    [ case sym of
                                        NS ns -> do
                                            ns_rep <- getNSymId ns
                                            return (strstr "NS " . shows ns_rep)
                                        TS ts -> do
                                            ts_rep <- getTSymId ts
                                            return (strstr "TS " . shows ts_rep)
                                    | sym <- rhs
                                    ]
                                return $ strcat
                                    [ strstr "(("
                                    , shows q
                                    , strstr ", "
                                    , shows tsym_id
                                    , strstr "), Reduce ("
                                    , shows lhs_rep
                                    , strstr ", ["
                                    , ppunc ", " rhs_rep
                                    , strstr "]))"
                                    ]
                            Accept -> return $ strcat
                                [ strstr "(("
                                , shows q
                                , strstr ", "
                                , shows tsym_id
                                , strstr "), Accept)"
                                ]
                        | (tsym_id, action) <- mSort (\pair1 -> \pair2 -> fst pair1 <= fst pair2) pairs'
                        ]
                | (q, pairs) <- formatTable (Map.toAscList (getActionTable lalr1))
                ]
            tellLine (strstr "        , getActionTable = YMap.fromAscList " . plist 12 action_table_rep)
            table2 <- lift $ sequence
                [ fmap (ppunc ", ") $ do
                    pairs' <- sequence
                        [ do
                            nsym_id <- getNSymId nsym
                            return (nsym_id, p)
                        | (nsym, p) <- pairs
                        ]
                    return
                        [ strcat
                            [ strstr "(("
                            , shows q
                            , strstr ", "
                            , shows nsym_id
                            , strstr "), "
                            , shows p
                            , strstr ")"
                            ]
                        | (nsym_id, p) <- mSort (\pair1 -> \pair2 -> fst pair1 <= fst pair2) pairs'
                        ]
                | (q, pairs) <- formatTable (Map.toAscList (getReduceTable lalr1))
                ]
            tellLine (strstr "        , getReduceTable = YMap.fromAscList " . plist 12 table2)
            tellLine (strstr "        }")
            -- tellLine (strstr "")
            -- tellLine (strstr "{-")
            -- tellLine (pprint 0 collection)
            -- tellLine (strstr "")
            -- tellLine (strstr "_First = " . plist 4 [ shows (withZero $ pprint 0 (NS ns) . strstr " +-> {" . ppunc ", " [ pprint 0 (TS t) | Just t <- Set.toList (unTerminalSet tss) ] . strstr "}") | (ns, tss) <- Map.toAscList _First ])
            -- tellLine (strstr "")
            -- tellLine (strstr "_LA = " . plist 4 [ shows (withZero $ strstr "( q = " . shows q . strstr ", [" . pprint 0 (NS lhs) . strstr " ::= " . ppunc " " (map (pprint 0) rhs) . strstr "] ) +-> {" . ppunc ", " [ pprint 0 (TS t) | t <- Set.toList tss ] . strstr "}") | ((q, (lhs, rhs)), tss) <- mSort (<=) _LA ])
            -- tellLine (strstr "-}")
            return ()
        return y_out

main :: IO ()
main = do
    dir <- shelly ("PGS =<< ")
    let dir_rev = reverse dir
    let dir' = if take 4 dir_rev == "txt." then reverse (drop 4 dir_rev) else dir
    yblocks <- P.runP dir (many (readBlock <* many P.lend) <* P.eof)
    case yblocks of
        Nothing -> putStrLn ("parse failed")
        Just yblocks' -> do
            let res = genParser yblocks'
            case runIdentity (runExceptT res) of
                Left err -> do
                    writeFileNow (dir' ++ ".failed") err
                    shelly ("PGS >>= tell (generating-failed)")
                    return ()
                Right delta -> do
                    writeFileNow (dir' ++ ".hs") delta
                    shelly ("PGS >>= tell (the-parser-has-been-generated)")
                    return ()

instance Semigroup TerminalSet where
    ts1 <> ts2 = if isNullable ts1 then TerminalSet (Set.delete Nothing (unTerminalSet ts1) `Set.union` unTerminalSet ts2) else ts1 where
        isNullable :: TerminalSet -> Bool
        isNullable = Set.member Nothing . unTerminalSet

instance Monoid TerminalSet where
    mempty = TerminalSet (Set.singleton Nothing)

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
                        , mSort (\pair1 -> \pair2 -> snd pair1 < snd pair2) ((sym, p) : [ (sym', p') | ((q', sym'), p') <- triples' ])
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

instance Show Conflict where
    show = flip (shows) ""
    showList = undefined
    showsPrec _ (Conflict (action1, action2) (q, t) (Cannonical0 vertices root edges))
        = strcat
            [ strstr "couldn't resolve conflict:" . nl
            , strstr "  ? " . pprint 0 action1 . strstr " v.s. " . pprint 0 action2 . strstr " at { state = " . shows q . strstr ", terminal = " . pprint 0 (TS t) . strstr " }" . nl
            , strstr "  ? collection = {" . nl
            , strstr "    getParserSInfo :: ParserS -> ParserSInfo" . nl
            , ppunc "\n"
                [ ppunc "\n"
                    [ strstr "    getParserSInfo " . shows q . strstr " = ParserSInfo"
                    , strstr "        { myItems = " . plist 12 (map (quotify . pprint 0) items)
                    , strstr "        , myNexts = " . plist 12 [ quotify (pprint 0 sym . strstr " +-> " . shows p) | (sym, p) <- maybe [] id (lookup q formatedEdges) ]
                    , strstr "        }"
                    ]
                | (items, q) <- formatedVertices
                ]
            , nl . strstr "  }" . nl
            ]
        where
            formatedVertices :: [([LR0Item], ParserS)]
            formatedVertices = do
                (q, items) <- Map.toAscList vertices
                return (Set.toAscList items, q)
            formatedEdges :: [(ParserS, [(Sym, ParserS)])]
            formatedEdges = do
                triples <- splitUnless (\triple1 -> \triple2 -> fst (fst triple1) == fst (fst triple2)) (Map.toAscList edges)
                case triples of
                    [] -> []
                    ((q, sym), p) : triples' -> return
                        ( q
                        , mSort (\pair1 -> \pair2 -> snd pair1 < snd pair2) ((sym, p) : [ (sym', p') | ((q', sym'), p') <- triples' ])
                        )
