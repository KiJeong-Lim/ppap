module Hol.BETA.Notation
    ( NotationDB
    , FixityKind (..)
    , Precedence
    , initial
    , merge
    , mergeWithShadows
    , declarationDelta
    , addFixity
    , fixityAliases
    , addAbbrev
    , addNotation
    , lookupFixity
    , fixityList
    , declaredFixityList
    , viewerFixity
    , notationCheckOper
    , constructViewerWithDB
    , foldType
    , foldTerm
    , compileTypeTemplate
    , ExpansionDB
    , emptyExpansionDB
    , initialExpansionDB
    , mergeExpansion
    , mergeExpansionWithShadows
    , addTypeAbbrevDecl
    , addTermNotationDecl
    , lookupTypeAbbrev
    , lookupTermNotation
    , typeAbbrevList
    , termNotationList
    , declaredTypeAbbrevList
    , declaredTermNotationList
    , ExpansionError (..)
    , validateExpansionDB
    , expandTermRepChecked
    , expandTypeRepChecked
    , expandTermRep
    , expandTypeRep
    , foldTermAsNode
    , tryFoldType
    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.PlanHolLexer
import Hol.BETA.TermNode

type Precedence = Int

data FixityKind
    = FK_Prefix
    | FK_InfixL
    | FK_InfixR
    | FK_InfixN
    deriving (Eq, Show)

data EntryKind
    = EK_Type
    | EK_Term
    deriving (Eq, Ord, Show)

data FoldEntry
    = FoldEntry
        { _feName :: !SmallId
        , _feParams :: ![LargeId]
        , _feRhs :: !TermNode             -- type RHS pre-compiled to TermNode
        , _feSeq :: !Int
        , _feKind :: !EntryKind
        }
    deriving ()

data NotationDB
    = NotationDB
        { _fixity :: !(Map.Map SmallId (FixityKind, Precedence))
        , _declaredFixity :: !(Map.Map SmallId (FixityKind, Precedence))
        , _entries :: ![FoldEntry]
        , _declaredEntries :: !(Set.Set (EntryKind, SmallId))
        , _nextSeq :: !Int
        }
    deriving ()

compileTypeTemplate :: MonoType LargeId -> TermNode
compileTypeTemplate (TyVar x) = mkLVar (LV_Named x)
compileTypeTemplate (TyCon (TCon tc _)) = mkNCon tc
compileTypeTemplate (TyApp t1 t2) = mkNApp (compileTypeTemplate t1) (compileTypeTemplate t2)
compileTypeTemplate (TyMTV m) = mkLVar (LV_ty_var m)

initial :: NotationDB
initial = seededString { _declaredEntries = Set.empty } where
    seededString = addAbbrev "string" [] stringRhs seededFixity
    stringRhs :: MonoType LargeId
    stringRhs = TyApp (TyCon (TCon (TC_Named "list") (KArr Star Star))) (TyCon (TCon (TC_Named "char") Star))

    seededFixity :: NotationDB
    seededFixity = NotationDB
        { _fixity = seedFixities
        , _declaredFixity = Map.empty
        , _entries = []
        , _declaredEntries = Set.empty
        , _nextSeq = 0
        }

seedFixities :: Map.Map SmallId (FixityKind, Precedence)
seedFixities = Map.fromList
    [ ("Lambda", (FK_Prefix, 0))
    , (":-", (FK_InfixR, 0))
    , (";", (FK_InfixL, 1))
    , ("=>", (FK_InfixR, 2))
    , (",", (FK_InfixL, 3))
    , ("&", (FK_InfixL, 3))
    , ("->", (FK_InfixR, 4))
    , ("::", (FK_InfixR, 4))
    , ("pi", (FK_Prefix, 5))
    , ("sigma", (FK_Prefix, 5))
    , ("=", (FK_InfixN, 5))
    , ("=<", (FK_InfixN, 5))
    , ("<", (FK_InfixN, 5))
    , (">=", (FK_InfixN, 5))
    , (">", (FK_InfixN, 5))
    , ("is", (FK_InfixN, 5))
    , ("+", (FK_InfixL, 6))
    , ("-", (FK_InfixL, 6))
    , ("*", (FK_InfixL, 7))
    , ("/", (FK_InfixL, 7))
    ]

addFixity :: SmallId -> FixityKind -> Precedence -> NotationDB -> NotationDB
addFixity name k p db = db
    { _fixity = addAliases (_fixity db)
    , _declaredFixity = addAliases (_declaredFixity db)
    }
    where
        addAliases m = foldr (`Map.insert` (k, p)) m (fixityAliases name)

fixityAliases :: SmallId -> [SmallId]
fixityAliases "," = [",", "&"]
fixityAliases "&" = ["&", ","]
fixityAliases name = [name]

addAbbrev :: SmallId -> [LargeId] -> MonoType LargeId -> NotationDB -> NotationDB
addAbbrev name ps rhs = addEntry EK_Type name ps (compileTypeTemplate rhs)

addNotation :: SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addNotation name ps rhs db
    = assertNonnegativeIndices rhs `seq`
      addEntry EK_Term name ps rhs db

addEntry :: EntryKind -> SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addEntry kind name ps rhs db = db
    { _entries = entry : filter ((/= key) . entryKey) (_entries db)
    , _declaredEntries = Set.insert key (_declaredEntries db)
    , _nextSeq = n + 1
    }
  where
    n = _nextSeq db
    key = (kind, name)
    entry = FoldEntry
        { _feName = name
        , _feParams = ps
        , _feRhs = rhs
        , _feSeq = n
        , _feKind = kind
        }

entryKey :: FoldEntry -> (EntryKind, SmallId)
entryKey entry = (_feKind entry, _feName entry)

merge :: NotationDB -> NotationDB -> NotationDB
merge = mergeWithShadows [] []

mergeWithShadows :: [SmallId] -> [SmallId] -> NotationDB -> NotationDB -> NotationDB
mergeWithShadows shadowTypes shadowTerms older newer = NotationDB
        { _fixity  = Map.union (_declaredFixity newer) (_fixity older)
        , _declaredFixity = Map.union (_declaredFixity newer) (_declaredFixity older)
        , _entries = newEntries ++ retainedEntries
        , _declaredEntries = Set.union (_declaredEntries newer) (_declaredEntries older)
        , _nextSeq = max (_nextSeq older) (_nextSeq newer)
        }
    where
        forced = Set.fromList
            (map ((,) EK_Type) shadowTypes ++ map ((,) EK_Term) shadowTerms)
        genuinelyNew = Set.difference (_declaredEntries newer) (_declaredEntries older)
        accepted = Set.union forced genuinelyNew
        newEntries = filter ((`Set.member` accepted) . entryKey) (_entries newer)
        retainedEntries = filter ((`Set.notMember` accepted) . entryKey) (_entries older)

declarationDelta :: NotationDB -> ExpansionDB -> NotationDB -> NotationDB
declarationDelta fixityDecls expansionDecls effective = NotationDB
    { _fixity = _fixity fixityDecls
    , _declaredFixity = _declaredFixity fixityDecls
    , _entries = filter ((`Set.member` ownEntryKeys) . entryKey) (_entries effective)
    , _declaredEntries = ownEntryKeys
    , _nextSeq = _nextSeq effective
    }
    where
        ownEntryKeys = Set.fromList
            ( [ (EK_Type, name) | (name, _, _) <- declaredTypeAbbrevList expansionDecls ]
           ++ [ (EK_Term, name) | (name, _, _) <- declaredTermNotationList expansionDecls ]
            )

lookupFixity :: SmallId -> NotationDB -> Maybe (FixityKind, Precedence)
lookupFixity name db = Map.lookup name (_fixity db)

fixityList :: NotationDB -> [(SmallId, (FixityKind, Precedence))]
fixityList = Map.toList . _fixity

declaredFixityList :: NotationDB -> [(SmallId, (FixityKind, Precedence))]
declaredFixityList = Map.toList . _declaredFixity

viewerFixity :: SmallId -> (FixityKind, Precedence) -> (Fixity (), Precedence)
viewerFixity op (FK_Prefix, p) = (Prefix (op ++ " ") (), p)
viewerFixity op (FK_InfixL, p) = (InfixL () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixR, p) = (InfixR () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixN, p) = (InfixN () (" " ++ op ++ " ") (), p)

notationCheckOper :: NotationDB -> SmallId -> Maybe (Fixity (), Precedence)
notationCheckOper db con = fmap (viewerFixity displayed) fixity where
    fixity
        | quotedNamed = lookup lookupName (declaredFixityList db)
        | otherwise = lookupFixity lookupName db
    (lookupName, displayed, quotedNamed) = case con of
        '_' : '_' : rest -> (rest, rest, False)
        '`' : rest
            | not (null rest)
            , last rest == '`' -> (init rest, con, True)
        _ -> (con, con, False)

constructViewerWithDB :: NotationDB -> (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerWithDB db lookupName t =
    constructViewerCustom (notationCheckOper db) lookupName (foldTermAsNode db t)

foldType :: NotationDB -> MonoType LargeId -> ViewNode
foldType db = foldTerm db . compileTypeTemplate

foldTerm :: NotationDB -> TermNode -> ViewNode
foldTerm db = constructViewerCustom (const Nothing) (const Nothing) . foldTermAsNode db

tryMatch :: [FoldEntry] -> TermNode -> Maybe (EntryKind, SmallId, [TermNode])
tryMatch entries t
    = assertNonnegativeTerms (map _feRhs entries) `seq`
      assertNonnegativeIndices t `seq`
      firstJust
        [ do
            env <- matchTerm (_feParams e) (_feRhs e) t
            args <- traverse (`Map.lookup` env) (_feParams e)
            return (_feKind e, _feName e, args)
        | e <- entries
        ]

tryFoldType :: NotationDB -> MonoType Int -> Maybe (SmallId, [MonoType Int])
tryFoldType db t
    = case tryMatch typeEntries (monoTypeIntToNode t) of
        Just (EK_Type, name, argNodes) -> do
            args <- traverse nodeToMonoTypeInt argNodes
            return (name, args)
        _ -> Nothing
    where
        typeEntries = filter (\e -> _feKind e == EK_Type) (_entries db)

monoTypeIntToNode :: MonoType Int -> TermNode
monoTypeIntToNode (TyVar i) = mkLVar (LV_Named ("a_" ++ show i))
monoTypeIntToNode (TyMTV m) = mkLVar (LV_ty_var m)
monoTypeIntToNode (TyCon (TCon tc _)) = mkNCon tc
monoTypeIntToNode (TyApp t1 t2) = mkNApp (monoTypeIntToNode t1) (monoTypeIntToNode t2)

nodeToMonoTypeInt :: TermNode -> Maybe (MonoType Int)
nodeToMonoTypeInt term = assertNonnegativeIndices term `seq` go term where
    go (LVar (LV_ty_var m)) = Just (TyMTV m)
    go (NCon (TC tc) _) = Just (TyCon (TCon tc Star))
    go (NApp t1 t2 _) = TyApp <$> go t1 <*> go t2
    go _ = Nothing

foldTermAsNode :: NotationDB -> TermNode -> TermNode
foldTermAsNode db term
    = assertNonnegativeTerms (map _feRhs (_entries db)) `seq`
      assertNonnegativeIndices term `seq`
      go Set.empty term
  where
    go _ (NIdx i)
        | i < 0 = undefined
    go active t = tryHere active $ case t of
        NApp t1 t2 sl -> NApp (go active t1) (go active t2) sl
        NLam mhint ty body sl -> NLam mhint ty (go active body) sl
        Susp body env_n env_l mtv -> Susp (go active body) env_n env_l mtv
        _ -> t
    tryHere active t = case tryMatch available t of
        Just (kind, name, args) ->
            List.foldl' mkNApp head_ (map (go (Set.insert key active)) args)
          where
            key = (kind, name)
            head_ = case kind of
                EK_Type -> mkNCon (TC_Named name)
                EK_Term -> mkNCon (DC_Named name)
        Nothing -> t
      where
        -- A template such as @notation id X := X@ legitimately matches every
        -- term.  While rendering its captured arguments, disable that entry
        -- (and every enclosing fold entry) so presentation folding cannot
        -- recursively re-fold the very term it just captured.  Keeping the
        -- complete active set also terminates mutually overlapping catch-all
        -- templates without rejecting useful identity declarations.
        available = filter ((`Set.notMember` active) . entryKey) (_entries db)

matchTerm :: [LargeId] -> TermNode -> TermNode -> Maybe (Map.Map LargeId TermNode)
matchTerm params tmpl cand
    = assertNonnegativeIndices tmpl `seq`
        assertNonnegativeIndices cand `seq`
        go tmpl cand Map.empty
  where
    isParam (LV_Named n) = n `elem` params
    isParam _ = False
    go (LVar lv) c env
        | isParam lv
        = case Map.lookup n env of
            Nothing -> Just (Map.insert n c env)
            Just prev -> if prev == c then Just env else Nothing
        where
            LV_Named n = lv
    go (LVar lv1) (LVar lv2) env
        | lv1 == lv2 = Just env
        | otherwise = Nothing
    go (NCon c1 _) (NCon c2 _) env
        | c1 == c2 = Just env
        | otherwise = Nothing
    go (NIdx i) (NIdx j) env
        | i < 0 || j < 0 = undefined
        | i == j = Just env
        | otherwise = Nothing
    go (NApp a1 a2 _) (NApp b1 b2 _) env    
        = go a1 b1 env >>= go a2 b2
    go (NLam _ _ t1 _) (NLam _ _ t2 _) env
        = go t1 t2 env
    go _ _ _
        = Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs

data ExpansionDB
    = ExpansionDB
        { _typeAbbrevs :: !(Map.Map SmallId ([LargeId], TypeRep))
        , _termNotations :: !(Map.Map SmallId ([LargeId], TermRep))
        , _declaredTypeAbbrevs :: !(Set.Set SmallId)
        , _declaredTermNotations :: !(Set.Set SmallId)
        , _typeAbbrevOrder :: ![SmallId]
        , _termNotationOrder :: ![SmallId]
        }
    deriving ()

emptyExpansionDB :: ExpansionDB
emptyExpansionDB = ExpansionDB
    { _typeAbbrevs = Map.empty
    , _termNotations = Map.empty
    , _declaredTypeAbbrevs = Set.empty
    , _declaredTermNotations = Set.empty
    , _typeAbbrevOrder = []
    , _termNotationOrder = []
    }

mergeExpansion :: ExpansionDB -> ExpansionDB -> ExpansionDB
mergeExpansion older newer = mergeExpansionWithShadows
    (_typeAbbrevOrder newer) (_termNotationOrder newer) older newer

mergeExpansionWithShadows :: [SmallId] -> [SmallId] -> ExpansionDB -> ExpansionDB -> ExpansionDB
mergeExpansionWithShadows shadowTypes shadowTerms older newer = ExpansionDB
    { _typeAbbrevs = Map.union acceptedTypes (_typeAbbrevs older)
    , _termNotations = Map.union acceptedTerms (_termNotations older)
    , _declaredTypeAbbrevs = Set.union (_declaredTypeAbbrevs newer) (_declaredTypeAbbrevs older)
    , _declaredTermNotations = Set.union (_declaredTermNotations newer) (_declaredTermNotations older)
    , _typeAbbrevOrder = mergeOrder acceptedTypeNames (_typeAbbrevOrder older) (_typeAbbrevOrder newer)
    , _termNotationOrder = mergeOrder acceptedTermNames (_termNotationOrder older) (_termNotationOrder newer)
    }
    where
        acceptedTypeNames = Set.union (Set.fromList shadowTypes)
            (Set.difference (_declaredTypeAbbrevs newer) (_declaredTypeAbbrevs older))
        acceptedTermNames = Set.union (Set.fromList shadowTerms)
            (Set.difference (_declaredTermNotations newer) (_declaredTermNotations older))
        acceptedTypes = Map.restrictKeys (_typeAbbrevs newer) acceptedTypeNames
        acceptedTerms = Map.restrictKeys (_termNotations newer) acceptedTermNames
        mergeOrder accepted oldOrder newOrder =
            filter (`Set.notMember` accepted) oldOrder
                ++ filter (`Set.member` accepted) newOrder

initialExpansionDB :: ExpansionDB
initialExpansionDB = emptyExpansionDB
    { _typeAbbrevs = Map.singleton "string" ([], stringRhs) }
  where
    nullLoc :: SLoc
    nullLoc = SLoc (0, 0) (0, 0)
    stringRhs :: TypeRep
    stringRhs = RTyApp nullLoc (RTyCon nullLoc (TC_Named "list")) (RTyCon nullLoc (TC_Named "char"))

addTypeAbbrevDecl :: SmallId -> [LargeId] -> TypeRep -> ExpansionDB -> ExpansionDB
addTypeAbbrevDecl name params body db = db
    { _typeAbbrevs = Map.insert name (params, body) (_typeAbbrevs db)
    , _declaredTypeAbbrevs = Set.insert name (_declaredTypeAbbrevs db)
    , _typeAbbrevOrder = moveToEnd name (_typeAbbrevOrder db)
    }

addTermNotationDecl :: SmallId -> [LargeId] -> TermRep -> ExpansionDB -> ExpansionDB
addTermNotationDecl name params body db = db
    { _termNotations = Map.insert name (params, body) (_termNotations db)
    , _declaredTermNotations = Set.insert name (_declaredTermNotations db)
    , _termNotationOrder = moveToEnd name (_termNotationOrder db)
    }

moveToEnd :: Eq a => a -> [a] -> [a]
moveToEnd item items = filter (/= item) items ++ [item]

lookupTypeAbbrev :: SmallId -> ExpansionDB -> Maybe ([LargeId], TypeRep)
lookupTypeAbbrev name db = Map.lookup name (_typeAbbrevs db)

lookupTermNotation :: SmallId -> ExpansionDB -> Maybe ([LargeId], TermRep)
lookupTermNotation name db = Map.lookup name (_termNotations db)

typeAbbrevList :: ExpansionDB -> [(SmallId, [LargeId], TypeRep)]
typeAbbrevList db =
    [ (name, ps, rhs)
    | name <- undeclaredNames ++ _typeAbbrevOrder db
    , Just (ps, rhs) <- [Map.lookup name (_typeAbbrevs db)]
    ]
    where
        undeclaredNames = Map.keys
            (Map.withoutKeys (_typeAbbrevs db) (_declaredTypeAbbrevs db))

termNotationList :: ExpansionDB -> [(SmallId, [LargeId], TermRep)]
termNotationList db =
    [ (name, ps, rhs)
    | name <- undeclaredNames ++ _termNotationOrder db
    , Just (ps, rhs) <- [Map.lookup name (_termNotations db)]
    ]
    where
        undeclaredNames = Map.keys
            (Map.withoutKeys (_termNotations db) (_declaredTermNotations db))

declaredTypeAbbrevList :: ExpansionDB -> [(SmallId, [LargeId], TypeRep)]
declaredTypeAbbrevList db =
    [ (name, ps, rhs)
    | name <- _typeAbbrevOrder db
    , Just (ps, rhs) <- [Map.lookup name (_typeAbbrevs db)]
    ]

declaredTermNotationList :: ExpansionDB -> [(SmallId, [LargeId], TermRep)]
declaredTermNotationList db =
    [ (name, ps, rhs)
    | name <- _termNotationOrder db
    , Just (ps, rhs) <- [Map.lookup name (_termNotations db)]
    ]

unfoldlTermApp :: TermRep -> (TermRep, [TermRep])
unfoldlTermApp = go [] where
    go acc (RApp _ t1 t2) = go (t2 : acc) t1
    go acc t = (t, acc)

unfoldlTypeApp :: TypeRep -> (TypeRep, [TypeRep])
unfoldlTypeApp = go [] where
    go acc (RTyApp _ t1 t2) = go (t2 : acc) t1
    go acc t = (t, acc)

reapplyTerm :: SLoc -> TermRep -> [TermRep] -> TermRep
reapplyTerm loc = List.foldl' (\acc arg -> RApp loc acc arg)

reapplyType :: SLoc -> TypeRep -> [TypeRep] -> TypeRep
reapplyType loc = List.foldl' (\acc arg -> RTyApp loc acc arg)

freeNamesOfTermRep :: TermRep -> Set.Set LargeId
freeNamesOfTermRep t = case t of
    R_wc _ -> Set.empty
    RVar _ x -> Set.singleton x
    RCon _ (DC_Named x) -> Set.singleton x
    RCon _ _ -> Set.empty
    RApp _ t1 t2 -> Set.union (freeNamesOfTermRep t1) (freeNamesOfTermRep t2)
    RAbs _ x body -> Set.delete x (freeNamesOfTermRep body)
    RPrn _ t' -> freeNamesOfTermRep t'

allNamesOfTermRep :: TermRep -> Set.Set LargeId
allNamesOfTermRep t = case t of
    R_wc _ -> Set.empty
    RVar _ x -> Set.singleton x
    RCon _ (DC_Named x) -> Set.singleton x
    RCon _ _ -> Set.empty
    RApp _ t1 t2 -> Set.union (allNamesOfTermRep t1) (allNamesOfTermRep t2)
    RAbs _ x body -> Set.insert x (allNamesOfTermRep body)
    RPrn _ t' -> allNamesOfTermRep t'

freshNameAvoiding :: Set.Set LargeId -> LargeId -> LargeId
freshNameAvoiding avoid base
    | not (Set.member base avoid) = base
    | otherwise = go (1 :: Int)
    where
        go n = if Set.member candidate avoid then go (n + 1) else candidate where
            candidate = base ++ "_" ++ show n

substTermRep :: Map.Map LargeId TermRep -> TermRep -> TermRep
substTermRep env t = case t of
    R_wc loc -> R_wc loc
    RVar loc x -> case Map.lookup x env of
        Just replacement -> replacement
        Nothing -> RVar loc x
    RCon loc c -> RCon loc c
    RApp loc t1 t2 -> RApp loc (substTermRep env t1) (substTermRep env t2)
    RAbs loc x body
        | Set.member x rhsFV -> RAbs loc x' (substTermRep env' renamed)
        | otherwise -> RAbs loc x (substTermRep env' body)
        where
            env' = Map.delete x env
            rhsFV = Set.unions (map freeNamesOfTermRep (Map.elems env'))
            avoid = Set.unions [rhsFV, allNamesOfTermRep body, Map.keysSet env']
            x' = freshNameAvoiding avoid x
            renamed = renameBoundTermRep x x' body
    RPrn loc t' -> RPrn loc (substTermRep env t')

renameBoundTermRep :: LargeId -> LargeId -> TermRep -> TermRep
renameBoundTermRep old new = go where
    go term = case term of
        R_wc loc -> R_wc loc
        RVar loc x
            | x == old -> RVar loc new
            | otherwise -> RVar loc x
        RCon loc (DC_Named x)
            | x == old -> RCon loc (DC_Named new)
            | otherwise -> RCon loc (DC_Named x)
        RCon loc con -> RCon loc con
        RApp loc left right -> RApp loc (go left) (go right)
        RAbs loc x body
            | x == old -> RAbs loc x body
            | otherwise -> RAbs loc x (go body)
        RPrn loc body -> RPrn loc (go body)

substTypeRep :: Map.Map LargeId TypeRep -> TypeRep -> TypeRep
substTypeRep env t = case t of
    RTyVar loc x -> case Map.lookup x env of
        Just replacement -> replacement
        Nothing -> RTyVar loc x
    RTyCon loc c -> RTyCon loc c
    RTyApp loc t1 t2 -> RTyApp loc (substTypeRep env t1) (substTypeRep env t2)
    RTyPrn loc t' -> RTyPrn loc (substTypeRep env t')

data ExpansionError
    = TypeExpansionCycle SLoc [SmallId]
    | TermExpansionCycle SLoc [SmallId]
    deriving (Eq, Show)

validateExpansionDB :: ExpansionDB -> Either ExpansionError ()
validateExpansionDB db = do
    mapM_ validateType (declaredTypeAbbrevList db)
    mapM_ validateTerm (declaredTermNotationList db)
    where
        validateType (name, params, rhs) = do
            let loc = typeRepLoc rhs
                head_ = RTyCon loc (TC_Named name)
                args = map (RTyVar loc) params
                applied = reapplyType loc head_ args
            _ <- expandTypeRepChecked db applied
            return ()
        validateTerm (name, params, rhs) = do
            let loc = termRepLoc rhs
                head_ = RCon loc (DC_Named name)
                args = map (RVar loc) params
                applied = reapplyTerm loc head_ args
            _ <- expandTermRepChecked db applied
            return ()

typeRepLoc :: TypeRep -> SLoc
typeRepLoc (RTyVar loc _) = loc
typeRepLoc (RTyCon loc _) = loc
typeRepLoc (RTyApp loc _ _) = loc
typeRepLoc (RTyPrn loc _) = loc

termRepLoc :: TermRep -> SLoc
termRepLoc (R_wc loc) = loc
termRepLoc (RVar loc _) = loc
termRepLoc (RCon loc _) = loc
termRepLoc (RApp loc _ _) = loc
termRepLoc (RAbs loc _ _) = loc
termRepLoc (RPrn loc _) = loc

rebaseTermRep :: SLoc -> TermRep -> TermRep
rebaseTermRep callLoc term = case term of
    R_wc _ -> R_wc callLoc
    RVar _ name -> RVar callLoc name
    RCon _ con -> RCon callLoc con
    RApp _ left right -> RApp callLoc (rebaseTermRep callLoc left) (rebaseTermRep callLoc right)
    RAbs _ name body -> RAbs callLoc name (rebaseTermRep callLoc body)
    RPrn _ body -> RPrn callLoc (rebaseTermRep callLoc body)

expansionCycle :: SmallId -> [SmallId] -> [SmallId]
expansionCycle name active = name : reverse (takeWhile (/= name) active) ++ [name]

expandTermRepChecked :: ExpansionDB -> TermRep -> Either ExpansionError TermRep
expandTermRepChecked db = go [] Set.empty where
    templateNames = Set.unions
        ( Map.keysSet (_termNotations db)
        : [ Set.union (Set.fromList params) (allNamesOfTermRep body)
          | (params, body) <- Map.elems (_termNotations db)
          ]
        )
    go active bound t = case t of
        RApp loc _ _ -> do
            args' <- traverse (go active bound) args
            case head_ of
                RCon hloc (DC_Named name)
                    | Set.member name bound ->
                        Right (reapplyTerm loc head_ args')
                    | otherwise -> case lookupTermNotation name db of
                        Just (params, body)
                            | name `elem` active -> Left (TermExpansionCycle hloc (expansionCycle name active))
                            | length args' >= length params -> expandFull name hloc loc params body args'
                            | otherwise -> expandPartial name hloc params body args'
                        Nothing -> Right (reapplyTerm loc head_ args')
                _ -> do
                    head' <- go active bound head_
                    return (reapplyTerm loc head' args')
            where
                (head_, args) = unfoldlTermApp t
                expandFull name headLoc loc params body expandedArgs = do
                    let (consumed, remaining) = splitAt (length params) expandedArgs
                        callLoc = List.foldl' (<>) headLoc (map termRepLoc consumed)
                        env = Map.fromList (zip params consumed)
                    expanded <- go (name : active) bound (substTermRep env (rebaseTermRep callLoc body))
                    return (reapplyTerm loc expanded remaining)
                expandPartial name headLoc params body expandedArgs = do
                    let n = length expandedArgs
                        consumed = expandedArgs
                        taken = take n params
                        remaining = drop n params
                        callLoc = List.foldl' (<>) headLoc (map termRepLoc consumed)
                        env = Map.fromList (zip taken consumed)
                        etaExpanded = List.foldr (\p acc -> RAbs callLoc p acc) (rebaseTermRep callLoc body) remaining
                    go (name : active) bound (substTermRep env etaExpanded)
        RCon loc (DC_Named name)
            | Set.member name bound -> Right (RCon loc (DC_Named name))
            | otherwise -> case lookupTermNotation name db of
                Just (params, body)
                    | name `elem` active -> Left (TermExpansionCycle loc (expansionCycle name active))
                    | List.null params -> go (name : active) bound (rebaseTermRep loc body)
                    | otherwise -> do
                        inner <- go (name : active) bound (rebaseTermRep loc body)
                        return (List.foldr (\p acc -> RAbs loc p acc) inner params)
                Nothing -> Right (RCon loc (DC_Named name))
        RAbs loc x body -> do
            -- Give the source binder a private temporary spelling before any
            -- template is copied underneath it.  Existing bound occurrences
            -- are renamed with it, whereas a free same-named constructor
            -- introduced by a notation remains @x@ and therefore cannot be
            -- captured at the later desugaring pass.  Restore the user's
            -- spelling when expansion introduced no such free name.
            let avoid = Set.unions
                    [ Set.singleton x
                    , bound
                    , templateNames
                    , allNamesOfTermRep body
                    ]
                private = freshNameAvoiding avoid x
                renamedBody = renameBoundTermRep x private body
            expandedBody <- go active (Set.insert private bound) renamedBody
            if Set.member x (freeNamesOfTermRep expandedBody) then
                return (RAbs loc private expandedBody)
            else
                return (RAbs loc x (renameBoundTermRep private x expandedBody))
        RPrn loc t' -> RPrn loc <$> go active bound t'
        _ -> Right t

expandTypeRepChecked :: ExpansionDB -> TypeRep -> Either ExpansionError TypeRep
expandTypeRepChecked db = go [] where
    go active t = case t of
        RTyApp loc _ _ -> do
            args' <- traverse (go active) args
            case head_ of
                RTyCon hloc (TC_Named name) -> case lookupTypeAbbrev name db of
                    Just (params, body)
                        | name `elem` active -> Left (TypeExpansionCycle hloc (expansionCycle name active))
                        | length args' >= length params -> expandFull name loc params body args'
                        | otherwise -> Right (reapplyType loc head_ args')
                    Nothing -> Right (reapplyType loc head_ args')
                _ -> do
                    head' <- go active head_
                    return (reapplyType loc head' args')
            where
                (head_, args) = unfoldlTypeApp t
                expandFull name loc params body expandedArgs = do
                    let (consumed, remaining) = splitAt (length params) expandedArgs
                        env = Map.fromList (zip params consumed)
                    expanded <- go (name : active) (substTypeRep env body)
                    return (reapplyType loc expanded remaining)
        RTyCon loc (TC_Named name) -> case lookupTypeAbbrev name db of
            Just (params, body)
                | name `elem` active -> Left (TypeExpansionCycle loc (expansionCycle name active))
                | List.null params -> go (name : active) body
                | otherwise -> Right (RTyCon loc (TC_Named name))
            Nothing -> Right (RTyCon loc (TC_Named name))
        RTyPrn loc t' -> RTyPrn loc <$> go active t'
        _ -> Right t

expandTermRep :: ExpansionDB -> TermRep -> TermRep
expandTermRep db term = either (const term) id (expandTermRepChecked db term)

expandTypeRep :: ExpansionDB -> TypeRep -> TypeRep
expandTypeRep db typ = either (const typ) id (expandTypeRepChecked db typ)
