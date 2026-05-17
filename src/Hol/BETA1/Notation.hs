module Hol.BETA1.Notation
    ( NotationDB
    , FixityKind (..)
    , Precedence
    , initial
    , addFixity
    , addAbbrev
    , addNotation
    , lookupFixity
    , viewerFixity
    , notationCheckOper
    , constructViewerWithDB
    , foldType
    , foldTerm
    , compileTypeTemplate
    -- §1.6.3 desugar-time expansion (parsing direction)
    , ExpansionDB
    , emptyExpansionDB
    , initialExpansionDB
    , addTypeAbbrevDecl
    , addTermNotationDecl
    , lookupTypeAbbrev
    , lookupTermNotation
    , expandTermRep
    , expandTypeRep
    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Hol.BETA1.Constant
import Hol.BETA1.Header
import Hol.BETA1.PlanHolLexer
import Hol.BETA1.TermNode

-- =============================================================
-- Public types
-- =============================================================

type Precedence = Int

data FixityKind
    = FK_Prefix
    | FK_InfixL
    | FK_InfixR
    | FK_InfixN
    deriving (Eq, Show)

-- Abbreviations vs notations differ only in *intended display*: an
-- abbreviated type rendered through ViewTCon, an abbreviated term
-- through ViewDCon. The matcher operates uniformly on TermNodes
-- because BETA1 compiles types to terms (the viewer erases the type
-- coordinates).
data EntryKind
    = EK_Type
    | EK_Term
    deriving (Eq, Show)

data FoldEntry = FoldEntry
    { _feName :: !SmallId
    , _feParams :: ![LargeId]
    , _feRhs :: !TermNode             -- type RHS pre-compiled to TermNode
    , _feSeq :: !Int
    , _feKind :: !EntryKind
    }

-- Opaque database. Internally:
--   * `Map SmallId (FixityKind, Precedence)` keyed by the operator's
--     surface spelling (matches `ViewDCon`/`ViewTCon`'s `SmallId`
--     payload, which is what the viewer's `formatView` pass has to
--     match on).
--   * `[FoldEntry]` for type/term abbreviations (newest first),
--   * a monotonic counter for `_seq`.
data NotationDB = NotationDB
    { _fixity :: !(Map.Map SmallId (FixityKind, Precedence))
    , _entries :: ![FoldEntry]
    , _nextSeq :: !Int
    }

-- =============================================================
-- Compilation: MonoType template -> TermNode template
-- =============================================================

-- Mirrors `Hol.BETA1.Compiler.convertType` but specialised to named
-- type variables. A `TyVar x` becomes `LVar (LV_Named x)`; the same
-- convention used for term notation parameters. The kind on each
-- `TyCon` is discarded — the matcher only cares about identity at
-- the `TypeConstructor` level (see `Eq TCon`).
compileTypeTemplate :: MonoType LargeId -> TermNode
compileTypeTemplate (TyVar x) = mkLVar (LV_Named x)
compileTypeTemplate (TyCon (TCon tc _)) = mkNCon tc
compileTypeTemplate (TyApp t1 t2) =
    mkNApp (compileTypeTemplate t1) (compileTypeTemplate t2)
compileTypeTemplate (TyMTV m) = mkLVar (LV_ty_var m)

-- =============================================================
-- Seeded initial DB
-- =============================================================

-- §1.5 fixity defaults + §1.6.5 built-in `abbrev string := list char`.
-- Built-ins are inserted *first*, so user-declared entries naturally
-- outrank them under "last declared wins" (§2.7.4).
initial :: NotationDB
initial = addAbbrev "string" [] stringRhs seededFixity
  where
    stringRhs :: MonoType LargeId
    stringRhs =
        TyApp
            (TyCon (TCon (TC_Named "list") (KArr Star Star)))
            (TyCon (TCon (TC_Named "char") Star))

    seededFixity :: NotationDB
    seededFixity = NotationDB
        { _fixity = Map.fromList seeds
        , _entries = []
        , _nextSeq = 0
        }

    seeds :: [(SmallId, (FixityKind, Precedence))]
    seeds =
        [ ("Lambda", (FK_Prefix, 0))
        , (":-", (FK_InfixR, 0))
        , (";", (FK_InfixL, 1))
        , ("=>", (FK_InfixR, 2))
        , (",", (FK_InfixL, 3))
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
        , ("+", (FK_InfixN, 6))
        , ("-", (FK_InfixN, 6))
        , ("*", (FK_InfixN, 7))
        , ("/", (FK_InfixN, 7))
        ]

-- =============================================================
-- Registration
-- =============================================================

addFixity :: SmallId -> FixityKind -> Precedence -> NotationDB -> NotationDB
addFixity name k p db = db { _fixity = Map.insert name (k, p) (_fixity db) }

addAbbrev :: SmallId -> [LargeId] -> MonoType LargeId -> NotationDB -> NotationDB
addAbbrev name ps rhs = addEntry EK_Type name ps (compileTypeTemplate rhs)

addNotation :: SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addNotation name ps rhs = addEntry EK_Term name ps rhs

addEntry :: EntryKind -> SmallId -> [LargeId] -> TermNode -> NotationDB -> NotationDB
addEntry kind name ps rhs db =
    let n = _nextSeq db
        entry = FoldEntry
            { _feName = name
            , _feParams = ps
            , _feRhs = rhs
            , _feSeq = n
            , _feKind = kind
            }
    in db
        { _entries = entry : _entries db
        , _nextSeq = n + 1
        }

lookupFixity :: SmallId -> NotationDB -> Maybe (FixityKind, Precedence)
lookupFixity name db = Map.lookup name (_fixity db)

-- §2.6: convert a NotationDB-resolved `(kind, prec)` into the
-- `Fixity ()` shape the viewer's `formatView` pass consumes. Spacing
-- is added uniformly: ` op ` for infix, `op ` for prefix. The
-- separator strings remain in sync with what the legacy hard-coded
-- `checkOper` produced for the BETA1 built-ins.
viewerFixity :: SmallId -> (FixityKind, Precedence) -> (Fixity (), Precedence)
viewerFixity op (FK_Prefix, p) = (Prefix (op ++ " ") (), p)
viewerFixity op (FK_InfixL, p) = (InfixL () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixR, p) = (InfixR () (" " ++ op ++ " ") (), p)
viewerFixity op (FK_InfixN, p) = (InfixN () (" " ++ op ++ " ") (), p)

-- §2.6 fixity resolver for the viewer. Looks `con` up in `db._fixity`
-- and packages the result into the `Fixity ()` shape `formatView`
-- consumes. A miss falls back to `Nothing` (caller treats the
-- constant as a prefix application, matching the legacy behaviour).
-- The `__` prefix that `TermNode.makeView` attaches to every
-- `DC_Named`/`TC_Named` rendering is stripped before the lookup so
-- that user declarations (which carry the bare spelling) match.
notationCheckOper :: NotationDB -> SmallId -> Maybe (Fixity (), Precedence)
notationCheckOper db con =
    let stripped = case con of
            '_' : '_' : rest -> rest
            _ -> con
    in fmap (viewerFixity stripped) (lookupFixity stripped db)

-- §2.6: the NotationDB-aware viewer. Identical to
-- `TermNode.constructViewer` except that the fixity table is read
-- out of `db` (built by the desugarer from the program's §1.5
-- `infix*`/`prefix` declarations) rather than `defaultCheckOper`.
constructViewerWithDB :: NotationDB -> (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerWithDB db = constructViewerCustom (notationCheckOper db)

-- =============================================================
-- Folding
-- =============================================================

-- `foldType` is a thin convenience: compile the MonoType to TermNode
-- and dispatch to `foldTerm`. Both surface to the same matcher.
foldType :: NotationDB -> MonoType LargeId -> ViewNode
foldType db = foldTerm db . compileTypeTemplate

foldTerm :: NotationDB -> TermNode -> ViewNode
foldTerm db t = case tryMatch (_entries db) t of
    Just (kind, name, args) ->
        let head_ = case kind of
                EK_Type -> ViewTCon name
                EK_Term -> ViewDCon name
            app = case kind of
                EK_Type -> ViewTApp
                EK_Term -> ViewIApp
        in List.foldl' app head_ (map (foldTerm db) args)
    Nothing -> renderTerm db t

-- Minimal structural renderer. The full §2.6 viewer (rewriting,
-- type erasure, fixity-aware formatting) is implemented in
-- `Hol.BETA1.Viewer::constructViewerWith`; integrating fold into
-- that pipeline is a separate task. For now this renderer is enough
-- for §2.7 (T) error-message folding and matcher tests.
renderTerm :: NotationDB -> TermNode -> ViewNode
renderTerm _ (LVar (LV_ty_var u)) = ViewTVar ("?TV_" ++ show u)
renderTerm _ (LVar (LV_Unique u (DispHint mhint))) = ViewLVar (case mhint of Just s -> s; Nothing -> "?V_" ++ show u)
renderTerm _ (LVar (LV_Named v)) = ViewLVar v
renderTerm _ (NCon (DC d)) = ViewDCon (show d)
renderTerm _ (NCon (TC t)) = ViewTCon (show t)
renderTerm _ (NIdx i) = ViewIVar ("W_" ++ show i)
renderTerm db (NApp t1 t2) = ViewIApp (foldTerm db t1) (foldTerm db t2)
renderTerm db (NLam mhint _ t) =
    let name = case mhint of
            Just s -> s
            Nothing -> "x"
    in ViewIAbs name (foldTerm db t)
renderTerm db (Susp body _ _ _) = foldTerm db body

tryMatch
    :: [FoldEntry]
    -> TermNode
    -> Maybe (EntryKind, SmallId, [TermNode])
tryMatch entries t = firstJust
    [ do
        env <- matchTerm (_feParams e) (_feRhs e) t
        args <- traverse (`Map.lookup` env) (_feParams e)
        return (_feKind e, _feName e, args)
    | e <- entries
    ]

-- First-order pattern matching on TermNodes. A parameter named in
-- `params` appears as `LVar (LV_Named name)` inside the template and
-- is bound to whatever TermNode occupies the same position in the
-- candidate. Repeated parameters require structural equality. Lambda
-- bodies match structurally (de Bruijn indices preserved).
matchTerm
    :: [LargeId]
    -> TermNode
    -> TermNode
    -> Maybe (Map.Map LargeId TermNode)
matchTerm params tmpl cand = go tmpl cand Map.empty
  where
    isParam (LV_Named n) = n `elem` params
    isParam _ = False

    go (LVar lv) c env
        | isParam lv =
            let LV_Named n = lv
            in case Map.lookup n env of
                Nothing -> Just (Map.insert n c env)
                Just prev -> if prev == c then Just env else Nothing
    go (LVar lv1) (LVar lv2) env = if lv1 == lv2 then Just env else Nothing
    go (NCon c1) (NCon c2) env = if c1 == c2 then Just env else Nothing
    go (NIdx i) (NIdx j) env = if i == j then Just env else Nothing
    go (NApp a1 a2) (NApp b1 b2) env = do
        env1 <- go a1 b1 env
        go a2 b2 env1
    go (NLam _ _ t1) (NLam _ _ t2) env = go t1 t2 env
    go _ _ _ = Nothing

-- =============================================================
-- Utilities
-- =============================================================

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs

-- =============================================================
-- §1.6.3 ExpansionDB: parsing-direction abbreviations/notations
-- =============================================================
--
-- The viewer side of notations (NotationDB + foldTerm) works at the
-- TermNode level, after the type checker has fully resolved everything.
-- The parsing side has to run *before* the type checker — the body of a
-- notation is plain surface syntax that has to be substituted into the
-- caller's source-level tree so the type checker sees a single, fully
-- expanded expression. ExpansionDB carries the surface representation
-- (TermRep / TypeRep) that the desugarer needs.

data ExpansionDB = ExpansionDB
    { _typeAbbrevs :: !(Map.Map SmallId ([LargeId], TypeRep))
    , _termNotations :: !(Map.Map SmallId ([LargeId], TermRep))
    }

emptyExpansionDB :: ExpansionDB
emptyExpansionDB = ExpansionDB { _typeAbbrevs = Map.empty, _termNotations = Map.empty }

-- §1.6.5: BETA1 seeds `abbrev string := list char.` as the only
-- built-in abbreviation. Other built-ins (lists, naturals, chars) are
-- kernel constants, not notations.
initialExpansionDB :: ExpansionDB
initialExpansionDB = addTypeAbbrevDecl "string" [] stringRhs emptyExpansionDB where
    nullLoc :: SLoc
    nullLoc = SLoc (0, 0) (0, 0)
    stringRhs :: TypeRep
    stringRhs = RTyApp nullLoc (RTyCon nullLoc (TC_Named "list")) (RTyCon nullLoc (TC_Named "char"))

addTypeAbbrevDecl :: SmallId -> [LargeId] -> TypeRep -> ExpansionDB -> ExpansionDB
addTypeAbbrevDecl name params body db =
    db { _typeAbbrevs = Map.insert name (params, body) (_typeAbbrevs db) }

addTermNotationDecl :: SmallId -> [LargeId] -> TermRep -> ExpansionDB -> ExpansionDB
addTermNotationDecl name params body db =
    db { _termNotations = Map.insert name (params, body) (_termNotations db) }

lookupTypeAbbrev :: SmallId -> ExpansionDB -> Maybe ([LargeId], TypeRep)
lookupTypeAbbrev name db = Map.lookup name (_typeAbbrevs db)

lookupTermNotation :: SmallId -> ExpansionDB -> Maybe ([LargeId], TermRep)
lookupTermNotation name db = Map.lookup name (_termNotations db)

-- =============================================================
-- §1.6.3 expansion: surface-level recursive descent
-- =============================================================
--
-- Both expanders walk the surface tree bottom-up and, whenever they
-- find a head that matches a registered abbreviation/notation, splice
-- the body in place with capture-shadowing substitution (binders
-- inside the body remove the corresponding parameter from the env).
-- True capture-avoidance is not yet implemented — callers should use
-- parameter names that do not collide with any bound identifier in the
-- body. The 1st-cut limitation is documented in §1.6.3 of the spec.

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

substTermRep :: Map.Map LargeId TermRep -> TermRep -> TermRep
substTermRep env t = case t of
    R_wc loc -> R_wc loc
    RVar loc x -> case Map.lookup x env of
        Just replacement -> replacement
        Nothing -> RVar loc x
    RCon loc c -> RCon loc c
    RApp loc t1 t2 -> RApp loc (substTermRep env t1) (substTermRep env t2)
    RAbs loc x body -> RAbs loc x (substTermRep (Map.delete x env) body)
    RPrn loc t' -> RPrn loc (substTermRep env t')

substTypeRep :: Map.Map LargeId TypeRep -> TypeRep -> TypeRep
substTypeRep env t = case t of
    RTyVar loc x -> case Map.lookup x env of
        Just replacement -> replacement
        Nothing -> RTyVar loc x
    RTyCon loc c -> RTyCon loc c
    RTyApp loc t1 t2 -> RTyApp loc (substTypeRep env t1) (substTypeRep env t2)
    RTyPrn loc t' -> RTyPrn loc (substTypeRep env t')

-- Recursively expand every notation occurrence in a TermRep.
-- Application heads are checked first; on a successful match the body
-- is substituted and re-expanded (so chained notations compose).
expandTermRep :: ExpansionDB -> TermRep -> TermRep
expandTermRep db = go where
    go t = case t of
        RApp loc _ _ ->
            let (head_, args) = unfoldlTermApp t
                args' = map go args
            in case head_ of
                RCon hloc (DC_Named name) -> case lookupTermNotation name db of
                    Just (params, body)
                        | length args' >= length params ->
                            let (consumed, remaining) = splitAt (length params) args'
                                env = Map.fromList (zip params consumed)
                                expanded = go (substTermRep env body)
                            in reapplyTerm loc expanded remaining
                        | otherwise ->
                            -- §1.6.3 partial-application: η-abstract over the
                            -- unsupplied parameters so the surface tree the type
                            -- checker sees still type-checks. Fresh-enough names
                            -- come from the parameters themselves — `body` has no
                            -- free occurrences of these names except via the
                            -- substitution we are about to perform.
                            let n = length args'
                                consumed = args'
                                taken = take n params
                                remaining = drop n params
                                env = Map.fromList (zip taken consumed)
                                substituted = substTermRep env body
                                inner = go substituted
                            in List.foldr (\p acc -> RAbs loc p acc) inner remaining
                    Nothing -> reapplyTerm loc head_ args'
                _ -> reapplyTerm loc (go head_) args'
        RCon loc (DC_Named name) -> case lookupTermNotation name db of
            Just (params, body)
                | List.null params -> go body
                | otherwise ->
                    -- 0-arg occurrence of a parameterised notation: η-abstract.
                    List.foldr (\p acc -> RAbs loc p acc) (go body) params
            Nothing -> RCon loc (DC_Named name)
        RAbs loc x body -> RAbs loc x (go body)
        RPrn loc t' -> RPrn loc (go t')
        _ -> t

-- Recursively expand every type abbreviation occurrence in a TypeRep.
expandTypeRep :: ExpansionDB -> TypeRep -> TypeRep
expandTypeRep db = go where
    go t = case t of
        RTyApp loc _ _ ->
            let (head_, args) = unfoldlTypeApp t
                args' = map go args
            in case head_ of
                RTyCon hloc (TC_Named name) -> case lookupTypeAbbrev name db of
                    Just (params, body)
                        | length args' >= length params ->
                            let (consumed, remaining) = splitAt (length params) args'
                                env = Map.fromList (zip params consumed)
                                expanded = go (substTypeRep env body)
                            in reapplyType loc expanded remaining
                        | otherwise ->
                            -- §1.6.3 partial-application on the type level has
                            -- no clean analogue (no type-level lambdas in
                            -- BETA1), so we leave the unsaturated head alone.
                            -- The type checker will report the under-application
                            -- as a kinding error if it matters.
                            reapplyType loc head_ args'
                    Nothing -> reapplyType loc head_ args'
                _ -> reapplyType loc (go head_) args'
        RTyCon loc (TC_Named name) -> case lookupTypeAbbrev name db of
            Just (params, body)
                | List.null params -> go body
                | otherwise -> RTyCon loc (TC_Named name)
            Nothing -> RTyCon loc (TC_Named name)
        RTyPrn loc t' -> RTyPrn loc (go t')
        _ -> t
