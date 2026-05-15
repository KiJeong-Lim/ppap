module Hol.BETA1.Notation
    ( NotationDB
    , FixityKind (..)
    , Precedence
    , initial
    , addFixity
    , addAbbrev
    , addNotation
    , lookupFixity
    , foldType
    , foldTerm
    , compileTypeTemplate
    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Hol.BETA1.Constant
import Hol.BETA1.Header
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
--   * `Map Constant (FixityKind, Precedence)` for O(log n) fixity,
--   * `[FoldEntry]` for type/term abbreviations (newest first),
--   * a monotonic counter for `_seq`.
data NotationDB = NotationDB
    { _fixity :: !(Map.Map Constant (FixityKind, Precedence))
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

    seeds :: [(Constant, (FixityKind, Precedence))]
    seeds =
        [ (lo LO_ty_pi, (FK_Prefix, 0))
        , (lo LO_if, (FK_InfixR, 0))
        , (lo LO_or, (FK_InfixL, 1))
        , (lo LO_imply, (FK_InfixR, 2))
        , (lo LO_and, (FK_InfixL, 3))
        , (tc TC_Arrow, (FK_InfixR, 4))
        , (dc DC_Cons, (FK_InfixR, 4))
        , (lo LO_pi, (FK_Prefix, 5))
        , (lo LO_sigma, (FK_Prefix, 5))
        , (dc DC_eq, (FK_InfixN, 5))
        , (dc DC_le, (FK_InfixN, 5))
        , (dc DC_lt, (FK_InfixN, 5))
        , (dc DC_ge, (FK_InfixN, 5))
        , (dc DC_gt, (FK_InfixN, 5))
        , (lo LO_is, (FK_InfixN, 5))
        , (dc DC_plus, (FK_InfixN, 6))
        , (dc DC_minus, (FK_InfixN, 6))
        , (dc DC_mul, (FK_InfixN, 7))
        , (dc DC_div, (FK_InfixN, 7))
        ]

    lo :: LogicalOperator -> Constant
    lo op = DC (DC_LO op)
    dc :: DataConstructor -> Constant
    dc d = DC d
    tc :: TypeConstructor -> Constant
    tc t = TC t

-- =============================================================
-- Registration
-- =============================================================

addFixity :: Constant -> FixityKind -> Precedence -> NotationDB -> NotationDB
addFixity c k p db = db { _fixity = Map.insert c (k, p) (_fixity db) }

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

lookupFixity :: Constant -> NotationDB -> Maybe (FixityKind, Precedence)
lookupFixity c db = Map.lookup c (_fixity db)

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
-- `TermNode.hs::constructViewer`; integrating fold into that
-- pipeline is a separate task. For now this renderer is enough for
-- §2.7 (T) error-message folding and matcher tests.
renderTerm :: NotationDB -> TermNode -> ViewNode
renderTerm _ (LVar (LV_ty_var u)) = ViewTVar ("?TV_" ++ show u)
renderTerm _ (LVar (LV_Unique u (DispHint mhint))) = ViewLVar (case mhint of Just s -> s; Nothing -> "?V_" ++ show u)
renderTerm _ (LVar (LV_Named v)) = ViewLVar v
renderTerm _ (NCon (DC d)) = ViewDCon (show d)
renderTerm _ (NCon (TC t)) = ViewTCon (show t)
renderTerm _ (NIdx i) = ViewIVar ("W_" ++ show i)
renderTerm db (NApp t1 t2) = ViewIApp (foldTerm db t1) (foldTerm db t2)
renderTerm db (NLam mhint t) =
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
    go (NLam _ t1) (NLam _ t2) env = go t1 t2 env
    go _ _ _ = Nothing

-- =============================================================
-- Utilities
-- =============================================================

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs
