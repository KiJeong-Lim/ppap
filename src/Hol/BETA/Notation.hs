module Hol.BETA.Notation
    ( NotationDB
    , FixityKind (..)
    , Precedence
    , initial
    , merge
    , addFixity
    , addAbbrev
    , addNotation
    , lookupFixity
    , fixityList
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
    , addTypeAbbrevDecl
    , addTermNotationDecl
    , lookupTypeAbbrev
    , lookupTermNotation
    , typeAbbrevList
    , termNotationList
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
    deriving (Eq, Show)

data FoldEntry
    = FoldEntry
    { _feName :: !SmallId
    , _feParams :: ![LargeId]
    , _feRhs :: !TermNode             -- type RHS pre-compiled to TermNode
    , _feSeq :: !Int
    , _feKind :: !EntryKind
    } deriving ()

data NotationDB
    = NotationDB
    { _fixity :: !(Map.Map SmallId (FixityKind, Precedence))
    , _entries :: ![FoldEntry]
    , _nextSeq :: !Int
    } deriving ()


compileTypeTemplate :: MonoType LargeId -> TermNode
compileTypeTemplate (TyVar x) = mkLVar (LV_Named x)
compileTypeTemplate (TyCon (TCon tc _)) = mkNCon tc
compileTypeTemplate (TyApp t1 t2) = mkNApp (compileTypeTemplate t1) (compileTypeTemplate t2)
compileTypeTemplate (TyMTV m) = mkLVar (LV_ty_var m)


initial :: NotationDB
initial = addAbbrev "string" [] stringRhs seededFixity where
    stringRhs :: MonoType LargeId
    stringRhs = TyApp (TyCon (TCon (TC_Named "list") (KArr Star Star))) (TyCon (TCon (TC_Named "char") Star))

    seededFixity :: NotationDB
    seededFixity = NotationDB
        { _fixity = seedFixities
        , _entries = []
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
addFixity name k p db = db { _fixity = foldr (`Map.insert` (k, p)) (_fixity db) (fixityAliases name) }

fixityAliases :: SmallId -> [SmallId]
fixityAliases "," = [",", "&"]
fixityAliases "&" = ["&", ","]
fixityAliases name = [name]

addAbbrev :: SmallId -> [LargeId] -> MonoType LargeId -> NotationDB -> NotationDB
addAbbrev name ps rhs = addEntry EK_Type name ps (compileTypeTemplate rhs)

addNotation :: SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addNotation name ps rhs = addEntry EK_Term name ps rhs

addEntry :: EntryKind -> SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addEntry kind name ps rhs db
    = db { _entries = entry : _entries db, _nextSeq = n + 1}
    where
        n = _nextSeq db
        entry = FoldEntry
            { _feName = name
            , _feParams = ps
            , _feRhs = rhs
            , _feSeq = n
            , _feKind = kind
            }

merge :: NotationDB -> NotationDB -> NotationDB
merge older newer = NotationDB
    { _fixity  = Map.union (Map.filterWithKey nonSeed (_fixity newer)) (_fixity older)
    , _entries = _entries newer ++ _entries older
    , _nextSeq = max (_nextSeq older) (_nextSeq newer)
    }
    where
        nonSeed name fp = Map.lookup name seedFixities /= Just fp

lookupFixity :: SmallId -> NotationDB -> Maybe (FixityKind, Precedence)
lookupFixity name db = Map.lookup name (_fixity db)

fixityList :: NotationDB -> [(SmallId, (FixityKind, Precedence))]
fixityList = Map.toList . _fixity

viewerFixity :: SmallId -> (FixityKind, Precedence) -> (Fixity (), Precedence)
viewerFixity op (FK_Prefix, p) = (Prefix (op ++ " ") (), p)
viewerFixity op (FK_InfixL, p) = (InfixL () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixR, p) = (InfixR () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixN, p) = (InfixN () (" " ++ op ++ " ") (), p)

notationCheckOper :: NotationDB -> SmallId -> Maybe (Fixity (), Precedence)
notationCheckOper db con = fmap (viewerFixity stripped) (lookupFixity stripped db) where
    stripped = case con of
        '_' : '_' : rest -> rest
        _ -> con

constructViewerWithDB :: NotationDB -> (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerWithDB db lookupName t =
    constructViewerCustom (notationCheckOper db) lookupName (foldTermAsNode db t)


foldType :: NotationDB -> MonoType LargeId -> ViewNode
foldType db = foldTerm db . compileTypeTemplate

foldTerm :: NotationDB -> TermNode -> ViewNode
foldTerm db t = case tryMatch (_entries db) t of
    Just (kind, name, args) -> List.foldl' app head_ (map (foldTerm db) args) where
        head_ = case kind of
            EK_Type -> ViewTCon name
            EK_Term -> ViewDCon name
        app = case kind of
            EK_Type -> ViewTApp
            EK_Term -> ViewIApp
    Nothing -> renderTerm db t

renderTerm :: NotationDB -> TermNode -> ViewNode
renderTerm _ (LVar (LV_ty_var u)) = ViewTVar ("?TV_" ++ show u)
renderTerm _ (LVar (LV_Unique u (DispHint mhint))) = ViewLVar (case mhint of Just s -> s; Nothing -> "?V_" ++ show u)
renderTerm _ (LVar (LV_Named v)) = ViewLVar v
renderTerm _ (NCon (DC d) _) = ViewDCon (show d)
renderTerm _ (NCon (TC t) _) = ViewTCon (show t)
renderTerm _ (NIdx i) = ViewIVar ("W_" ++ show i)
renderTerm db (NApp t1 t2 _) = ViewIApp (foldTerm db t1) (foldTerm db t2)
renderTerm db (NLam mhint _ t _) = ViewIAbs name (foldTerm db t) where
    name = case mhint of
        Just s -> s
        Nothing -> "x"
renderTerm db (Susp body _ _ _) = foldTerm db body

tryMatch :: [FoldEntry] -> TermNode -> Maybe (EntryKind, SmallId, [TermNode])
tryMatch entries t = firstJust
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
nodeToMonoTypeInt (LVar (LV_ty_var m)) = Just (TyMTV m)
nodeToMonoTypeInt (NCon (TC tc) _) = Just (TyCon (TCon tc Star))
nodeToMonoTypeInt (NApp t1 t2 _) = TyApp <$> nodeToMonoTypeInt t1 <*> nodeToMonoTypeInt t2
nodeToMonoTypeInt _ = Nothing

foldTermAsNode :: NotationDB -> TermNode -> TermNode
foldTermAsNode db = go where
    go t = tryHere $ case t of
        NApp t1 t2 sl -> NApp (go t1) (go t2) sl
        NLam mhint ty body sl -> NLam mhint ty (go body) sl
        Susp body env_n env_l mtv -> Susp (go body) env_n env_l mtv
        _ -> t
    tryHere t = case tryMatch (_entries db) t of
        Just (kind, name, args) -> List.foldl' mkNApp head_ (map go args) where
            head_ = case kind of
                EK_Type -> mkNCon (TC_Named name)
                EK_Term -> mkNCon (DC_Named name)
        Nothing -> t

matchTerm :: [LargeId] -> TermNode -> TermNode -> Maybe (Map.Map LargeId TermNode)
matchTerm params tmpl cand = go tmpl cand Map.empty where
    isParam (LV_Named n) = n `elem` params
    isParam _ = False

    go (LVar lv) c env
        | isParam lv
        = case Map.lookup n env of
            Nothing -> Just (Map.insert n c env)
            Just prev -> if prev == c then Just env else Nothing
        where
            LV_Named n = lv
    go (LVar lv1) (LVar lv2) env = if lv1 == lv2 then Just env else Nothing
    go (NCon c1 _) (NCon c2 _) env = if c1 == c2 then Just env else Nothing
    go (NIdx i) (NIdx j) env = if i == j then Just env else Nothing
    go (NApp a1 a2 _) (NApp b1 b2 _) env = go a1 b1 env >>= go a2 b2
    go (NLam _ _ t1 _) (NLam _ _ t2 _) env = go t1 t2 env
    go _ _ _ = Nothing


firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs


data ExpansionDB
    = ExpansionDB
    { _typeAbbrevs :: !(Map.Map SmallId ([LargeId], TypeRep))
    , _termNotations :: !(Map.Map SmallId ([LargeId], TermRep))
    }

emptyExpansionDB :: ExpansionDB
emptyExpansionDB = ExpansionDB { _typeAbbrevs = Map.empty, _termNotations = Map.empty }

mergeExpansion :: ExpansionDB -> ExpansionDB -> ExpansionDB
mergeExpansion older newer = ExpansionDB
    { _typeAbbrevs   = Map.union (_typeAbbrevs   newer) (_typeAbbrevs   older)
    , _termNotations = Map.union (_termNotations newer) (_termNotations older)
    }

initialExpansionDB :: ExpansionDB
initialExpansionDB = addTypeAbbrevDecl "string" [] stringRhs emptyExpansionDB where
    nullLoc :: SLoc
    nullLoc = SLoc (0, 0) (0, 0)
    stringRhs :: TypeRep
    stringRhs = RTyApp nullLoc (RTyCon nullLoc (TC_Named "list")) (RTyCon nullLoc (TC_Named "char"))

addTypeAbbrevDecl :: SmallId -> [LargeId] -> TypeRep -> ExpansionDB -> ExpansionDB
addTypeAbbrevDecl name params body db = db { _typeAbbrevs = Map.insert name (params, body) (_typeAbbrevs db) }

addTermNotationDecl :: SmallId -> [LargeId] -> TermRep -> ExpansionDB -> ExpansionDB
addTermNotationDecl name params body db = db { _termNotations = Map.insert name (params, body) (_termNotations db) }

lookupTypeAbbrev :: SmallId -> ExpansionDB -> Maybe ([LargeId], TypeRep)
lookupTypeAbbrev name db = Map.lookup name (_typeAbbrevs db)

lookupTermNotation :: SmallId -> ExpansionDB -> Maybe ([LargeId], TermRep)
lookupTermNotation name db = Map.lookup name (_termNotations db)

typeAbbrevList :: ExpansionDB -> [(SmallId, [LargeId], TypeRep)]
typeAbbrevList db = [ (name, ps, rhs) | (name, (ps, rhs)) <- Map.toList (_typeAbbrevs db) ]

termNotationList :: ExpansionDB -> [(SmallId, [LargeId], TermRep)]
termNotationList db = [ (name, ps, rhs) | (name, (ps, rhs)) <- Map.toList (_termNotations db) ]


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

freeVarsOfTermRep :: TermRep -> Set.Set LargeId
freeVarsOfTermRep t = case t of
    R_wc _ -> Set.empty
    RVar _ x -> Set.singleton x
    RCon _ _ -> Set.empty
    RApp _ t1 t2 -> Set.union (freeVarsOfTermRep t1) (freeVarsOfTermRep t2)
    RAbs _ x body -> Set.delete x (freeVarsOfTermRep body)
    RPrn _ t' -> freeVarsOfTermRep t'

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
        | Map.member x env ->
            RAbs loc x (substTermRep (Map.delete x env) body)
        | Set.member x rhsFV -> RAbs loc x' (substTermRep env renamed)
        | otherwise ->
            RAbs loc x (substTermRep env body)
        where
            rhsFV = Set.unions (map freeVarsOfTermRep (Map.elems env))
            bodyFV = freeVarsOfTermRep body
            avoid = Set.unions [rhsFV, bodyFV, Map.keysSet env]
            x' = freshNameAvoiding avoid x
            renamed = substTermRep (Map.singleton x (RVar loc x')) body
    RPrn loc t' -> RPrn loc (substTermRep env t')

substTypeRep :: Map.Map LargeId TypeRep -> TypeRep -> TypeRep
substTypeRep env t = case t of
    RTyVar loc x -> case Map.lookup x env of
        Just replacement -> replacement
        Nothing -> RTyVar loc x
    RTyCon loc c -> RTyCon loc c
    RTyApp loc t1 t2 -> RTyApp loc (substTypeRep env t1) (substTypeRep env t2)
    RTyPrn loc t' -> RTyPrn loc (substTypeRep env t')

expandTermRep :: ExpansionDB -> TermRep -> TermRep
expandTermRep db = go where
    go t = case t of
        RApp loc _ _ ->
            case head_ of
                RCon hloc (DC_Named name) -> case lookupTermNotation name db of
                    Just (params, body)
                        | length args' >= length params -> expandFull loc params body args'
                        | otherwise -> expandPartial loc params body args'
                    Nothing -> reapplyTerm loc head_ args'
                _ -> reapplyTerm loc (go head_) args'
            where
                (head_, args) = unfoldlTermApp t
                args' = map go args
                expandFull loc params body args' = reapplyTerm loc expanded remaining where
                    (consumed, remaining) = splitAt (length params) args'
                    env = Map.fromList (zip params consumed)
                    expanded = go (substTermRep env body)
                expandPartial loc params body args' = List.foldr (\p acc -> RAbs loc p acc) inner remaining where
                    n = length args'
                    consumed = args'
                    taken = take n params
                    remaining = drop n params
                    env = Map.fromList (zip taken consumed)
                    substituted = substTermRep env body
                    inner = go substituted
        RCon loc (DC_Named name) -> case lookupTermNotation name db of
            Just (params, body)
                | List.null params -> go body
                | otherwise ->
                    List.foldr (\p acc -> RAbs loc p acc) (go body) params
            Nothing -> RCon loc (DC_Named name)
        RAbs loc x body -> RAbs loc x (go body)
        RPrn loc t' -> RPrn loc (go t')
        _ -> t

expandTypeRep :: ExpansionDB -> TypeRep -> TypeRep
expandTypeRep db = go where
    go t = case t of
        RTyApp loc _ _ ->
            case head_ of
                RTyCon hloc (TC_Named name) -> case lookupTypeAbbrev name db of
                    Just (params, body)
                        | length args' >= length params -> expandFull loc params body args'
                        | otherwise ->
                            reapplyType loc head_ args'
                    Nothing -> reapplyType loc head_ args'
                _ -> reapplyType loc (go head_) args'
            where
                (head_, args) = unfoldlTypeApp t
                args' = map go args
                expandFull loc params body args' = reapplyType loc expanded remaining where
                    (consumed, remaining) = splitAt (length params) args'
                    env = Map.fromList (zip params consumed)
                    expanded = go (substTypeRep env body)
        RTyCon loc (TC_Named name) -> case lookupTypeAbbrev name db of
            Just (params, body)
                | List.null params -> go body
                | otherwise -> RTyCon loc (TC_Named name)
            Nothing -> RTyCon loc (TC_Named name)
        RTyPrn loc t' -> RTyPrn loc (go t')
        _ -> t
