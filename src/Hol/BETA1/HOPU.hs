module Hol.BETA1.HOPU where

import Hol.BETA1.TermNode
import Hol.BETA1.Header
import Hol.BETA1.Constant
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.Char
import Data.Foldable
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algorithms
import Z.Utils

infix 4 +->

infix 6 :=?=:

type ScopeLevel = Int

type LogicVarSubst = VarBinding

type HasChanged = Bool

data Labeling
    = Labeling
        { _ConLabel :: IntMap.IntMap ScopeLevel
        , _VarLabel :: IntMap.IntMap ScopeLevel
        -- §3.4 CMTT: types of pi/sigma/ty_pi-introduced constants and
        -- variables. Populated by `Runtime.runLogicalOperator` and
        -- `Runtime.instantiateFact` from the `LamType` annotation on
        -- the surrounding lambda (see `Compiler.convertWithoutChecking`
        -- and `Compiler.makeUniversalClosure`). The kernel never reads
        -- these maps — they exist purely for debugger display and for
        -- `:assign`'s contextual type check.
        --
        -- `_VarTypes` only covers anonymous LVs (`LV_Unique`/`LV_ty_var`,
        -- which have an `Int` key). User-query variables `LV_Named` are
        -- stored in `_NamedTypes` (initialised at `execRuntime` from
        -- the typechecker's `assumptions`). `lookupLVarType` unifies
        -- the two so HOPU can ask "what is the type of this LV" without
        -- caring which constructor it was.
        , _ConTypes :: IntMap.IntMap (MonoType Int)
        , _VarTypes :: IntMap.IntMap (MonoType Int)
        , _NamedTypes :: Map.Map LargeId (MonoType Int)
        -- §3.4 CMTT: marks which `_VarLabel` entries are `LV_ty_var`s
        -- (the rest are `LV_Unique`s). Lets the debugger pick `?TV_<n>`
        -- vs `?V_<n>` for display even for LVs introduced by HOPU's
        -- `getNewLVar` (where the type-level flag is the only way to
        -- distinguish the two).
        , _TyVarKeys :: IntMap.IntMap ()
        -- §3.4 CMTT: the program's declared-constant type environment,
        -- stashed in `Labeling` so HOPU's type-inference helpers can
        -- look up `DC_Named c` types without threading `TypeEnv` through
        -- every HOPU entry point. Initialised once at `execRuntime` and
        -- never updated during search.
        , _TypeEnv :: TypeEnv
        }

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq, Ord, Show)

data HopuSol
    = HopuSol
        { _ChangedLabelingEnv :: Labeling
        , _MostGeneralUnifier :: LogicVarSubst
        }

data HopuFail
    = DownFail
    | UpFail
    | OccursCheckFail
    | FlexRigidFail
    | RigidRigidFail
    | BindFail
    | NotAPattern
    deriving (Eq, Ord, Show)

newtype VarBinding
    = VarBinding { unVarBinding :: Map.Map LogicVar TermNode }
    deriving (Eq, Ord, Show)

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

class HasLVar expr where
    accLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    bindVars :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LogicVarSubst -> expr -> expr

instance Labelable Constant where
    {-# INLINE enrollLabel #-}
    enrollLabel (DC (DC_Unique uni _)) level labeling = labeling { _ConLabel = IntMap.insert (unUnique uni) level (_ConLabel labeling) }
    enrollLabel _ _ labeling = labeling
    {-# INLINE updateLabel #-}
    updateLabel (DC (DC_Unique uni _)) level labeling = labeling { _ConLabel = IntMap.update (const (Just level)) (unUnique uni) (_ConLabel labeling) }
    updateLabel _ _ labeling = labeling
    {-# INLINE lookupLabel #-}
    lookupLabel (DC (DC_Unique uni _)) labeling = IntMap.findWithDefault maxBound (unUnique uni) (_ConLabel labeling)
    lookupLabel _ _ = 0

instance Labelable LogicVar where
    {-# INLINE enrollLabel #-}
    enrollLabel (LV_Named _) _ labeling = labeling
    enrollLabel v level labeling = labeling { _VarLabel = IntMap.insert (lvKey v) level (_VarLabel labeling) }
    {-# INLINE updateLabel #-}
    updateLabel (LV_Named _) _ labeling = labeling
    updateLabel v level labeling = labeling { _VarLabel = IntMap.update (const (Just level)) (lvKey v) (_VarLabel labeling) }
    {-# INLINE lookupLabel #-}
    lookupLabel (LV_Named _) _ = 0
    lookupLabel v labeling = IntMap.findWithDefault maxBound (lvKey v) (_VarLabel labeling)

{-# INLINE lvKey #-}
lvKey :: LogicVar -> Int
lvKey (LV_Unique u _) = unUnique u
lvKey (LV_ty_var u) = unUnique u
lvKey (LV_Named _) = error "lvKey: LV_Named has no Int key"

-- §3.4 CMTT: unified `LogicVar -> Maybe MonoType` lookup. Bridges
-- `_NamedTypes` (LV_Named, populated once at `execRuntime`) and
-- `_VarTypes` (LV_Unique/LV_ty_var, populated as the runtime introduces
-- fresh LVs at pi/sigma/ty_pi sites or via `getNewLVar`). Returns
-- `Nothing` for LVs the system has no type record for (e.g. an LV
-- introduced by HOPU before plan-1 type-threading is complete).
lookupLVarType :: LogicVar -> Labeling -> Maybe (MonoType Int)
lookupLVarType (LV_Named nm) lbl = Map.lookup nm (_NamedTypes lbl)
lookupLVarType v lbl = IntMap.lookup (lvKey v) (_VarTypes lbl)

-- §3.4 CMTT helpers for computing the type of a freshly minted
-- `common_head` in HOPU's pruning rules.

-- Strip `n` `(A -> B)` arrows from the front of a `MonoType`,
-- returning the stripped argument types and the residual result.
-- Returns `Nothing` if the type doesn't have enough arrows.
splitArrowsHOPU :: Int -> MonoType Int -> Maybe ([MonoType Int], MonoType Int)
splitArrowsHOPU 0 t = Just ([], t)
splitArrowsHOPU n (TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) t2)
    | n > 0 = do
        (params, result) <- splitArrowsHOPU (n - 1) t2
        return (t1 : params, result)
splitArrowsHOPU _ _ = Nothing

-- Build `arg1 -> arg2 -> ... -> result`.
mkArrowsHOPU :: [MonoType Int] -> MonoType Int -> MonoType Int
mkArrowsHOPU args result = foldr mkTyArrow result args

-- Look up the type of any constant the typechecker or runtime knows
-- about. Polymorphic constants (`Forall vars t`) return their inner
-- `MonoType` with `TyVar i` left intact — the debugger displays such
-- type variables as `a_i`, accepting the small inaccuracy in exchange
-- for not threading a `Unique` source into pure code.
lookupConType :: Constant -> Labeling -> Maybe (MonoType Int)
lookupConType (DC (DC_Unique uni _)) lbl = IntMap.lookup (unUnique uni) (_ConTypes lbl)
lookupConType (DC dc) lbl = case Map.lookup dc (_TypeEnv lbl) of
    Just (Forall _ ty) -> Just ty
    Nothing -> Nothing
lookupConType _ _ = Nothing

-- Best-effort type of a `TermNode`. Used by HOPU to populate the type
-- of a fresh `common_head` so the debugger can show it with the right
-- CMTT signature. `env` is a stack of binder types (innermost first)
-- accumulated as we descend through `NLam`s. Returns `Nothing` when
-- the term references something we don't have type info for (e.g. an
-- LV introduced by an earlier `getNewLVar` that itself was given `Nothing`).
typeOfTerm :: Labeling -> [MonoType Int] -> TermNode -> Maybe (MonoType Int)
typeOfTerm lbl env t = case t of
    LVar v -> lookupLVarType v lbl
    NCon c -> lookupConType c lbl
    NIdx i
        | i >= 0 && i < length env -> Just (env !! i)
        | otherwise -> Nothing
    NApp t1 t2 -> do
        ty1 <- typeOfTerm lbl env t1
        case ty1 of
            TyApp (TyApp (TyCon (TCon TC_Arrow _)) _) r -> Just r
            _ -> Nothing
    NLam _ (LamType (Just dom)) body -> do
        cod <- typeOfTerm lbl (dom : env) body
        Just (mkTyArrow dom cod)
    NLam _ _ _ -> Nothing
    Susp body _ _ _ -> typeOfTerm lbl env body
    NPresburgerCheck _ _ -> Just mkTyO

-- The HOPU pruning sites construct a substitution shaped like
--   var := \b_1 \b_2 ... \b_k. common_head a_1 a_2 ... a_m
-- where the lambda binders `b_1..b_k` come from `var`'s argument types.
-- `commonHeadType labeling var k args` computes the type
--   common_head : type(a_1) -> ... -> type(a_m) -> R
-- where `R` is `var`'s result type after stripping `k` arrows.
-- Args may be `NIdx i` (the deBruijn index of one of the introduced
-- lambdas, innermost first), a constant, an LVar, or an application —
-- `typeOfTerm` handles them uniformly using `_TypeEnv` for declared
-- constants and `_ConTypes`/`_VarTypes`/`_NamedTypes` for the rest.
commonHeadType :: Labeling -> LogicVar -> Int -> [TermNode] -> Maybe (MonoType Int)
commonHeadType labeling var k args = do
    varTy <- lookupLVarType var labeling
    (paramTypes, resultTy) <- splitArrowsHOPU k varTy
    -- Inner-most binder = last paramType; an `NIdx i` argument refers
    -- to `paramTypes !! (n - 1 - i)`. `typeOfTerm` follows the same
    -- convention with its `env` parameter.
    let env = reverse paramTypes
    argTypes <- traverse (typeOfTerm labeling env) args
    return (mkArrowsHOPU argTypes resultTy)

instance ZonkLVar Labeling where
    zonkLVar subst labeling = Map.foldlWithKey' applyBinding labeling (unVarBinding subst) where
        applyBinding :: Labeling -> LogicVar -> TermNode -> Labeling
        applyBinding lbl v t = case getLevel v lbl of
            Nothing -> lbl
            Just level -> Set.foldr (insertVarMin level) lbl (accLVarsTerm t Set.empty)
        getLevel :: LogicVar -> Labeling -> Maybe ScopeLevel
        getLevel (LV_Named _) _ = Just 0
        getLevel v lbl = IntMap.lookup (lvKey v) (_VarLabel lbl)
        insertVarMin :: ScopeLevel -> LogicVar -> Labeling -> Labeling
        insertVarMin _ (LV_Named _) lbl = lbl
        insertVarMin level v lbl = lbl { _VarLabel = IntMap.insertWith min (lvKey v) level (_VarLabel lbl) }

accLVarsTerm :: TermNode -> Set.Set LogicVar -> Set.Set LogicVar
accLVarsTerm (LVar v) = Set.insert v
accLVarsTerm (NCon _) = id
accLVarsTerm (NIdx _) = id
accLVarsTerm (NApp t1 t2) = accLVarsTerm t1 . accLVarsTerm t2
accLVarsTerm (NLam _ _ t) = accLVarsTerm t
accLVarsTerm (Susp t _ _ env) = accLVarsTerm t . accLVarsSuspEnv env
accLVarsTerm (NPresburgerCheck _ freeOf) = Set.union (Set.fromList (Map.elems freeOf))

accLVarsSuspEnv :: SuspEnv -> Set.Set LogicVar -> Set.Set LogicVar
accLVarsSuspEnv [] = id
accLVarsSuspEnv (Dummy _ : env) = accLVarsSuspEnv env
accLVarsSuspEnv (Binds t _ : env) = accLVarsTerm t . accLVarsSuspEnv env

instance HasLVar TermNode where
    accLVars = accLVarsTerm
    bindVars = flatten

instance HasLVar a => HasLVar [a] where
    accLVars = flip (foldr accLVars)
    bindVars = map . bindVars

instance HasLVar b => HasLVar (a, b) where
    accLVars = accLVars . snd
    bindVars = fmap . bindVars

instance HasLVar a => HasLVar (Map.Map k a) where
    accLVars = accLVars . Map.elems
    bindVars = Map.map . bindVars

instance Semigroup VarBinding where
    theta2 <> theta1
        | Map.null map2 = theta1
        | Map.null map1 = theta2
        | otherwise = VarBinding $! bindVars theta2 map1 `Map.union` map2
        where
            map1 = unVarBinding theta1
            map2 = unVarBinding theta2

instance Monoid VarBinding where
    mempty = VarBinding Map.empty

instance ZonkLVar VarBinding where
    zonkLVar subst binding = subst <> binding

instance ZonkLVar a => ZonkLVar [a] where
    zonkLVar = map . zonkLVar

instance HasLVar Disagreement where
    accLVars (lhs :=?=: rhs) = accLVars lhs . accLVars rhs
    bindVars theta (lhs :=?=: rhs) = bindVars theta lhs :=?=: bindVars theta rhs

instance ZonkLVar HopuSol where
    zonkLVar subst (HopuSol labeling binding) = HopuSol (zonkLVar subst labeling) (zonkLVar subst binding)

instance Outputable Labeling where
    pprint _ labeling
        = strcat
            [ strstr "Labeling\n"
            , strstr "    { _ConLabel = " . plist 8 [ strstr "DC_Unique " . shows k . strstr " *---> " . shows scp | (k, scp) <- IntMap.toList (_ConLabel labeling) ] . nl
            , strstr "    , _VarLabel = " . plist 8 [ strstr "Var " . shows k . strstr " *---> " . shows scp | (k, scp) <- IntMap.toList (_VarLabel labeling) ] . nl
            , strstr "    } "
            ]

instance Outputable VarBinding where
    pprint _ (VarBinding mapsto) = strstr "VarBinding " . plist 4 [ shows x . strstr " +-> " . shows t | (x, t) <- Map.toList mapsto ]

instance Outputable Disagreement where
    pprint prec (lhs :=?=: rhs)
        | prec > 5 = strstr "(" . go . strstr ")"
        | otherwise = go
        where
            go :: ShowS
            go = shows lhs . strstr " ~ " . shows rhs

{-# INLINE isRigidAtom #-}
isRigidAtom :: TermNode -> Bool
isRigidAtom (NCon (DC DC_wc)) = False
isRigidAtom (NCon {}) = True
isRigidAtom (NIdx {}) = True
isRigidAtom _ = False

{-# INLINE isTyLVar #-}
isTyLVar :: LogicVar -> Bool
isTyLVar (LV_ty_var {}) = True
isTyLVar _ = False

isPatternRespectTo :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternRespectTo v ts labeling = all isRigidAtom ts && areAllDistinct ts && and [ lookupLabel v labeling < lookupLabel c labeling | NCon c <- ts ]

down :: Monad m => [TermNode] -> [TermNode] -> StateT Labeling (ExceptT HopuFail m) [TermNode]
zs `down` ts = if downable then return indices else lift (throwE DownFail) where
    downable :: Bool
    downable = areAllDistinct ts && all isRigidAtom ts && areAllDistinct zs && all isRigidAtom zs
    indices :: [TermNode]
    indices = [ mkNIdx (length ts - i - 1) | z <- zs, i <- toList (z `List.elemIndex` ts) ]

up :: Monad m => [TermNode] -> LogicVar -> StateT Labeling (ExceptT HopuFail m) [TermNode]
ts `up` y = if upable then fmap findVisibles get else lift (throwE UpFail) where
    upable :: Bool
    upable = areAllDistinct ts && all isRigidAtom ts
    findVisibles :: Labeling -> [TermNode]
    findVisibles labeling = [ mkNCon c | NCon c <- ts, lookupLabel c labeling <= lookupLabel y labeling ]

bind :: [Maybe SmallId] -> LogicVar -> TermNode -> [TermNode] -> [Maybe SmallId] -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LogicVarSubst, TermNode)
bind outerHints var = go . rewrite HNF where
    go :: TermNode -> [TermNode] -> [Maybe SmallId] -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LogicVarSubst, TermNode)
    go (NLam mhint mty rhs') parameters bindHints = do
        (subst, lhs') <- go rhs' parameters (bindHints ++ [mhint])
        return (subst, mkNLamHintTy mhint mty lhs')
    go rhs parameters bindHints
        | (NCon (DC DC_wc), _) <- unfoldlNApp rhs
        = do
            labeling <- get
            -- §3.4 CMTT: the wildcard's type would equal `var`'s result
            -- type stripped by `length parameters` (we can't easily
            -- recover what arguments it stands in for here), so we err
            -- on the side of silence and leave the fresh LV's type
            -- unknown rather than risk recording a wrong one.
            h <- getNewLVar (isTyLVar var) (lookupLabel var labeling) Nothing
            return (mempty, h)
        | (rhs_head, rhs_tail) <- unfoldlNApp rhs
        , isRigidAtom rhs_head
        = do
            labeling <- get
            let lambda = length bindHints
                foldbind [] = return (mempty, [])
                foldbind (rhs_tail_elements : rhs_tail) = do
                    (subst, lhs_tail_elements) <- go (rewrite HNF rhs_tail_elements) parameters bindHints
                    (theta, lhs_tail) <- foldbind (bindVars subst rhs_tail)
                    return (theta <> subst, bindVars theta lhs_tail_elements : lhs_tail)
                getLhsHead lhs_arguments
                    | NCon con <- rhs_head
                    , lookupLabel var labeling >= lookupLabel con labeling
                    = return rhs_head
                    | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                    = return (mkNIdx (length lhs_arguments - idx - 1))
                    | otherwise
                    = lift (throwE FlexRigidFail)
            lhs_head <- getLhsHead ([ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0])
            (subst, lhs_tail) <- foldbind rhs_tail
            return (subst, List.foldl' mkNApp lhs_head lhs_tail)
        | (LVar var', rhs_tail) <- unfoldlNApp rhs
        = do
            when (var == var') $ lift (throwE OccursCheckFail)
            labeling <- get
            let lambda = length bindHints
                hints = outerHints ++ bindHints
                lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
                rhs_arguments = map (rewrite NF) rhs_tail
                common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                cmp_res = lookupLabel var labeling `compare` lookupLabel var' labeling
            if isPatternRespectTo var' rhs_arguments labeling then do
                (lhs_inner, rhs_inner) <- case cmp_res of
                    LT -> do
                        selected_rhs_parameters <- lhs_arguments `up` var'
                        selected_lhs_parameters <- selected_rhs_parameters `down` lhs_arguments
                        return (selected_lhs_parameters, selected_rhs_parameters)
                    _ -> do
                        selected_lhs_parameters <- rhs_arguments `up` var
                        selected_rhs_parameters <- selected_lhs_parameters `down` rhs_arguments
                        return (selected_lhs_parameters, selected_rhs_parameters)
                lhs_outer <- common_arguments `down` lhs_arguments
                rhs_outer <- common_arguments `down` rhs_arguments
                -- §3.4 CMTT: `common_head` is applied to (rhs_inner ++ rhs_outer)
                -- under `length rhs_arguments` lambdas whose binder types come
                -- from `var'`. `commonHeadType` derives the function type so
                -- the renderer can display the fresh LV with full CMTT context.
                let mCommonTy = commonHeadType labeling var' (length rhs_arguments) (rhs_inner ++ rhs_outer)
                common_head <- getNewLVar (isTyLVar var || isTyLVar var') (lookupLabel var labeling) mCommonTy
                theta <- lift $ var' +-> makeNestedNLamH (map (paramHint hints) rhs_arguments) (List.foldl' mkNApp common_head (rhs_inner ++ rhs_outer))
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head (lhs_inner ++ lhs_outer))
            else if cmp_res /= LT && all isRigidAtom rhs_arguments && and [ lookupLabel c labeling > lookupLabel var' labeling | NCon c <- rhs_arguments ] then do
                let mkBetaPattern (NCon c)
                        | lookupLabel c labeling <= lookupLabel var labeling = [mkNCon c]
                    mkBetaPattern z = [ mkNIdx (length lhs_arguments - 1 - i) | i <- toList (z `List.elemIndex` lhs_arguments) ]
                    isBetaPattern (NCon c)
                        | lookupLabel c labeling <= lookupLabel var labeling = True
                    isBetaPattern z = z `elem` common_arguments
                let betaArgs = [ mkNIdx (length rhs_arguments - i - 1) | i <- [0, 1 .. length rhs_arguments - 1], isBetaPattern (rhs_arguments !! i) ]
                    mCommonTy = commonHeadType labeling var' (length rhs_arguments) betaArgs
                common_head <- getNewLVar (isTyLVar var || isTyLVar var') (lookupLabel var labeling) mCommonTy
                theta <- lift $ var' +-> makeNestedNLamH (map (paramHint hints) rhs_arguments) (List.foldl' mkNApp common_head betaArgs)
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head (rhs_arguments >>= mkBetaPattern))
            else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)

-- Pull a display hint out of a rigid parameter, so that lambdas
-- synthesized by `mksubst` can recover source names from pi/sigma
-- instantiations and from outer lambdas peeled by `simplify`.
-- `outerHints` is the in-scope lambda hints (outermost first); a
-- `NIdx i` parameter refers to outerHints[length - 1 - i] when in
-- range. Returns `Nothing` for parameters that have no hint (e.g.
-- anonymous logic variables, type variables, applied terms, or
-- NIdx whose binder is out of `outerHints` reach).
paramHint :: [Maybe SmallId] -> TermNode -> Maybe SmallId
paramHint _ (NCon (DC (DC_Unique _ (DispHint mh)))) = mh
paramHint _ (LVar (LV_Unique _ (DispHint mh))) = mh
paramHint outerHints (NIdx i)
    | i >= 0 && i < n = outerHints !! (n - 1 - i)
    where
        n = length outerHints
paramHint _ _ = Nothing

mksubst :: [Maybe SmallId] -> LogicVar -> TermNode -> [TermNode] -> Labeling -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
mksubst outerHints var rhs parameters labeling = catchE (Just . uncurry (flip HopuSol) <$> runStateT (dispatch (rewrite NF rhs) parameters) labeling) handleErr where
    dispatch :: TermNode -> [TermNode] -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) LogicVarSubst
    dispatch rhs parameters
        | (rhsLamHints, rhs') <- viewNestedNLamH rhs
        , (LVar var', rhs_tail) <- unfoldlNApp rhs'
        , var == var'
        = do
            labeling <- get
            let lambda = length rhsLamHints
                n = length parameters + lambda
                normalizedParams = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ]
                lhs_arguments = normalizedParams ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
                rhs_arguments = map (rewrite NF) rhs_tail
                common_arguments = [ mkNIdx (n - i - 1) | i <- [0, 1 .. n - 1], lhs_arguments !! i == rhs_arguments !! i ]
            if lhs_arguments == rhs_arguments then
                return mempty
            else do
                unless (isPatternRespectTo var' rhs_arguments labeling) $ lift (throwE NotAPattern)
                -- §3.4 CMTT: the substitution wraps `common_head common_arguments`
                -- in `length normalizedParams + length rhsLamHints` lambdas whose
                -- binder types come from `var`'s type (var == var' here).
                let mCommonTy = commonHeadType labeling var' (length normalizedParams + length rhsLamHints) common_arguments
                common_head <- getNewLVar (isTyLVar var || isTyLVar var') (lookupLabel var labeling) mCommonTy
                theta <- lift $ var' +-> makeNestedNLamH (map (paramHint outerHints) normalizedParams ++ rhsLamHints) (List.foldl' mkNApp common_head common_arguments)
                modify (zonkLVar theta)
                return theta
{-
        | null parameters && canView labeling rhs
        = do -- ?- F = G x\ H y\ 1.
            theta <- lift $ var +-> rhs
            modify (zonkLVar theta)
            return theta
-}
        | otherwise
        = do
            labeling <- get
            let n = length parameters
                lhs_arguments = map (rewrite NF) parameters
            unless (isPatternRespectTo var lhs_arguments labeling) $ lift (throwE NotAPattern)
            (subst, lhs) <- bind outerHints var rhs parameters []
            theta <- lift $ var +-> makeNestedNLamH (map (paramHint outerHints) lhs_arguments) lhs
            modify (zonkLVar theta)
            return (theta <> subst)
    handleErr :: HopuFail -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err
    canView :: Labeling -> TermNode -> Bool
    canView labeling = go where
        go :: TermNode -> Bool
        go (NLam _ _ t1) = go t1
        go (NApp t1 t2) = go t1 && go t2
        go (NCon c) = lookupLabel var labeling >= lookupLabel c labeling
        go (LVar x) = lookupLabel var labeling >= lookupLabel x labeling

simplify :: [Disagreement] -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
simplify = flip loop mempty . zip (repeat []) where
    loop :: [([Maybe SmallId], Disagreement)] -> LogicVarSubst -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
    loop [] subst labeling = return ([], HopuSol labeling subst)
    loop ((l, lhs :=?=: rhs) : disagreements) subst labeling = dispatch l (rewrite NF lhs) (rewrite NF rhs) where
        dispatch :: [Maybe SmallId] -> TermNode -> TermNode -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
        dispatch l lhs rhs
            | (lhsHints, lhs') <- viewNestedNLamH lhs
            , (rhsHints, rhs') <- viewNestedNLamH rhs
            , not (null lhsHints) && not (null rhsHints)
            = let lambda1 = length lhsHints
                  lambda2 = length rhsHints
                  lambda = min lambda1 lambda2
              in dispatch (l ++ take lambda lhsHints) (makeNestedNLamH (drop lambda lhsHints) lhs') (makeNestedNLamH (drop lambda rhsHints) rhs')
            | (lhsHints, lhs') <- viewNestedNLamH lhs
            , not (null lhsHints)
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigidAtom rhs_head
            = let lambda1 = length lhsHints
              in dispatch (l ++ lhsHints) lhs' (List.foldl' mkNApp (rewriteWithSusp rhs_head 0 lambda1 [] HNF) ([ mkSusp rhs_tail_element 0 lambda1 [] | rhs_tail_element <- rhs_tail ] ++ map mkNIdx [lambda1 - 1, lambda1 - 2 .. 0]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhsHints, rhs') <- viewNestedNLamH rhs
            , isRigidAtom lhs_head
            , not (null rhsHints)
            = let lambda2 = length rhsHints
              in dispatch (l ++ rhsHints) (List.foldl' mkNApp (rewriteWithSusp lhs_head 0 lambda2 [] HNF) ([ mkSusp lhs_tail_element 0 lambda2 [] | lhs_tail_element <- lhs_tail ] ++ map mkNIdx [lambda2 - 1, lambda2 - 2 .. 0])) rhs'
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigidAtom lhs_head && isRigidAtom rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then loop ([ (l, lhs' :=?=: rhs') | (lhs', rhs') <- zip lhs_tail rhs_tail ] ++ disagreements) subst labeling
                else lift (throwE RigidRigidFail)
            | lhs == rhs
            = do
                put True
                loop disagreements subst labeling
            | (LVar var, parameters) <- unfoldlNApp lhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst l var rhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (bindVars subst' disagreements) (subst' <> subst) labeling'
            | (LVar var, parameters) <- unfoldlNApp rhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst l var lhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (bindVars subst' disagreements) (subst' <> subst) labeling'
            | (NCon (DC DC_wc), parameters) <- unfoldlNApp lhs
            = do
                put True
                loop disagreements subst labeling
            | (NCon (DC DC_wc), parameters) <- unfoldlNApp rhs
            = do
                put True
                loop disagreements subst labeling
            | otherwise
            = solveNext
        solveNext :: StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
        solveNext = do
            (disagreements', HopuSol labeling' subst') <- loop disagreements mempty labeling
            return (bindVars subst' (makeNestedNLamH l lhs :=?=: makeNestedNLamH l rhs) : disagreements', HopuSol labeling' (subst' <> subst))

runHOPU :: Labeling -> [Disagreement] -> UniqueT IO (Maybe ([Disagreement], HopuSol))
runHOPU = go where
    loop :: ([Disagreement], HopuSol) -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
    loop (disagreements, HopuSol labeling subst)
        | null disagreements = return (disagreements, HopuSol labeling subst)
        | otherwise = do
            (disagreements', HopuSol labeling' subst') <- simplify disagreements labeling
            let result = (disagreements', HopuSol labeling' (subst' <> subst))
            has_changed <- get
            if has_changed then put False >> loop result else return result
    go :: Labeling -> [Disagreement] -> UniqueT IO (Maybe ([Disagreement], HopuSol))
    go labeling disagreements = do
        output <- runExceptT (runStateT (loop (disagreements, HopuSol labeling mempty)) False)
        case output of
            Left _ -> return Nothing
            Right (result, _) -> return (Just result)

getLVars :: HasLVar expr => expr -> Set.Set LogicVar
getLVars = flip accLVars Set.empty

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding mapsto)
    | Map.null mapsto = id
    | otherwise = go . rewrite NF
    where
        go :: TermNode -> TermNode
        go (LVar v) = case Map.lookup v mapsto of
            Just t -> t
            Nothing -> LVar v
        go t@(NCon _) = t
        go t@(NIdx _) = t
        go (NApp t1 t2) = mkNApp (go t1) (go t2)
        go (NLam h ty t) = mkNLamHintTy h ty (go t)
        go t = t

(+->) :: Monad m => LogicVar -> TermNode -> ExceptT HopuFail m VarBinding
v +-> t
    | LVar v == t' = return (VarBinding $! Map.empty)
    | Set.null fvs = return (VarBinding $! Map.singleton v t')
    | v `Set.member` fvs = throwE OccursCheckFail
    | otherwise = return (VarBinding $! Map.singleton v t')
    where
        t' :: TermNode
        t' = etaReduce (rewrite NF t)
        fvs :: Set.Set LogicVar
        fvs = getLVars t'

-- §3.4 CMTT: caller passes the (best-effort) inferred type of the
-- new LV. `Nothing` means "type unknown", which the CMTT renderer
-- shows as `?`. Records `IsTypeLevel` into `_TyVarKeys` so the
-- renderer can pick `?TV_<n>` vs `?V_<n>` later.
getNewLVar :: MonadUnique m => IsTypeLevel -> ScopeLevel -> Maybe (MonoType Int) -> StateT Labeling m TermNode
getNewLVar is_ty label mty = do
    u <- getUnique
    let sym = if is_ty then LV_ty_var u else LV_Unique u noHint
    sym `seq` modify (enrollLabel sym label)
    when is_ty $ modify (\lbl -> lbl { _TyVarKeys = IntMap.insert (unUnique u) () (_TyVarKeys lbl) })
    case mty of
        Just ty -> modify (\lbl -> lbl { _VarTypes = IntMap.insert (unUnique u) ty (_VarTypes lbl) })
        Nothing -> return ()
    return (mkLVar sym)

etaReduce :: TermNode -> TermNode
etaReduce = go . rewrite NF where
    isFreeIn :: DeBruijn -> TermNode -> Bool
    isFreeIn i (NIdx j) = i == j
    isFreeIn i (NApp t1 t2) = isFreeIn i t1 || isFreeIn i t2
    isFreeIn i (NLam _ _ t1) = isFreeIn (i + 1) t1
    isFreeIn i _ = False
    decr :: TermNode -> TermNode
    decr (LVar x) = mkLVar x
    decr (NIdx i) = if i > 0 then mkNIdx (i - 1) else error "etaReduce.decr: unreachable..."
    decr (NCon c) = mkNCon c
    decr (NApp t1 t2) = mkNApp (decr t1) (decr t2)
    decr (NLam h ty t1) = mkNLamHintTy h ty (decr t1)
    go :: TermNode -> TermNode
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam h ty t1) = case go t1 of
        NApp t1' (NIdx 0)
            | not (isFreeIn 0 t1') -> decr t1'
        t1' -> mkNLamHintTy h ty t1'
    go t = t
