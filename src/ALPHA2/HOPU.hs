module ALPHA2.HOPU where

import ALPHA2.TermNode
import ALPHA2.Header
import ALPHA2.Constant
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.Char
import Data.Foldable
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
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving (Eq, Ord, Show)

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq, Ord, Show)

data HopuSol
    = HopuSol
        { _ChangedLabelingEnv :: Labeling
        , _MostGeneralUnifier :: LogicVarSubst
        }
    deriving (Eq, Ord, Show)

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
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.update (const (Just level)) atom (_ConLabel labeling) }
    lookupLabel atom = maybe (theDefaultLevel atom) id . Map.lookup atom . _ConLabel where
        theDefaultLevel :: Constant -> ScopeLevel
        theDefaultLevel (DC (DC_Unique _)) = maxBound
        theDefaultLevel _ = 0

instance Labelable LogicVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.update (const (Just level)) atom (_VarLabel labeling) }
    lookupLabel atom = maybe (theDefaultLevel atom) id . Map.lookup atom . _VarLabel where
        theDefaultLevel :: LogicVar -> ScopeLevel
        theDefaultLevel (LV_Named _) = 0
        theDefaultLevel (LV_ty_var _) = maxBound
        theDefaultLevel (LV_Unique _) = maxBound

instance ZonkLVar Labeling where
    zonkLVar subst labeling
        = labeling
            { _VarLabel = Map.fromAscList
                [ mkstrict
                    ( v
                    , foldr min (lookupLabel v labeling)
                        [ level'
                        | (v', t') <- Map.toList mapsto
                        , v `Set.member` getLVars t'
                        , level' <- toList (Map.lookup v' varlabel)
                        ]
                    )
                | v <- Set.toAscList (Map.keysSet mapsto `Set.union` Map.keysSet varlabel)
                ]
            }
        where
            mapsto :: Map.Map LogicVar TermNode
            mapsto = unVarBinding subst
            varlabel :: Map.Map LogicVar ScopeLevel
            varlabel = _VarLabel labeling
            mkstrict :: (LogicVar, ScopeLevel) -> (LogicVar, ScopeLevel)
            mkstrict pair = snd pair `seq` pair

instance HasLVar TermNode where
    accLVars = go . rewrite NF where
        go :: TermNode -> Set.Set LogicVar -> Set.Set LogicVar
        go (LVar v) = Set.insert v
        go (NCon c) = id
        go (NIdx i) = id
        go (NApp t1 t2) = go t1 . go t2
        go (NLam t) = go t
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
    theta2 <> theta1 = VarBinding $! map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = unVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = unVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = bindVars theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = VarBinding $! map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

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
            , strstr "    { _ConLabel = " . plist 8 [ shows (LVar x) . strstr " *---> " . shows scp | (x, scp) <- Map.toList (_VarLabel labeling) ] . nl
            , strstr "    , _VarLabel = " . plist 8 [ shows (NCon c) . strstr " *---> " . shows scp | (c, scp) <- Map.toList (_ConLabel labeling) ] . nl
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

isRigidAtom :: TermNode -> Bool
isRigidAtom (NCon (DC DC_wc)) = False
isRigidAtom (NCon {}) = True
isRigidAtom (NIdx {}) = True
isRigidAtom _ = False

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

bind :: LogicVar -> TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LogicVarSubst, TermNode)
bind var = go . rewrite HNF where
    go :: TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LogicVarSubst, TermNode)
    go rhs parameters lambda
        | (lambda', rhs') <- viewNestedNLam rhs
        , lambda' > 0
        = do
            (subst, lhs') <- go rhs' parameters (lambda + lambda')
            return (subst, makeNestedNLam lambda' lhs')
        | (NCon (DC DC_wc), _) <- unfoldlNApp rhs
        = do
            labeling <- get
            h <- getNewLVar (isTyLVar var) (lookupLabel var labeling)
            return (mempty, h)
        | (rhs_head, rhs_tail) <- unfoldlNApp rhs
        , isRigidAtom rhs_head
        = do
            labeling <- get
            let foldbind [] = return (mempty, [])
                foldbind (rhs_tail_elements : rhs_tail) = do
                    (subst, lhs_tail_elements) <- go (rewrite HNF rhs_tail_elements) parameters lambda
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
            let lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
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
                common_head <- getNewLVar (isTyLVar var) (lookupLabel var labeling)
                theta <- lift $ var' +-> makeNestedNLam (length rhs_tail) (List.foldl' mkNApp common_head (rhs_inner ++ rhs_outer))
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head (lhs_inner ++ lhs_outer))
            else if cmp_res /= LT && all isRigidAtom rhs_arguments && and [ lookupLabel c labeling > lookupLabel var' labeling | NCon c <- rhs_arguments ] then do
                let mkBetaPattern (NCon c)
                        | lookupLabel c labeling <= lookupLabel var labeling = [mkNCon c]
                    mkBetaPattern z = [ mkNIdx (length lhs_arguments - 1 - i) | i <- toList (z `List.elemIndex` lhs_arguments) ]
                    isBetaPattern (NCon c)
                        | lookupLabel c labeling <= lookupLabel var labeling = True
                    isBetaPattern z = z `elem` common_arguments
                common_head <- getNewLVar (isTyLVar var) (lookupLabel var labeling)
                theta <- lift $ var' +-> makeNestedNLam (length rhs_arguments) (List.foldl' mkNApp common_head [ mkNIdx (length rhs_arguments - i - 1) | i <- [0, 1 .. length rhs_arguments - 1], isBetaPattern (rhs_arguments !! i) ])
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head (rhs_arguments >>= mkBetaPattern))
            else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)

mksubst :: LogicVar -> TermNode -> [TermNode] -> Labeling -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
mksubst var rhs parameters labeling = catchE (Just . uncurry (flip HopuSol) <$> runStateT (dispatch (rewrite NF rhs) parameters) labeling) handleErr where
    dispatch :: TermNode -> [TermNode] -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) LogicVarSubst
    dispatch rhs parameters
        | (lambda, rhs') <- viewNestedNLam rhs
        , (LVar var', rhs_tail) <- unfoldlNApp rhs'
        , var == var'
        = do
            labeling <- get
            let n = length parameters + lambda
                lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
                rhs_arguments = map (rewrite NF) rhs_tail
                common_arguments = [ mkNIdx (n - i - 1) | i <- [0, 1 .. n - 1], lhs_arguments !! i == rhs_arguments !! i ]
            if lhs_arguments == rhs_arguments then
                return mempty
            else do
                unless (isPatternRespectTo var' rhs_arguments labeling) $ lift (throwE NotAPattern)
                common_head <- getNewLVar (isTyLVar var) (lookupLabel var labeling)
                theta <- lift $ var' +-> makeNestedNLam n (List.foldl' mkNApp common_head common_arguments)
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
            (subst, lhs) <- bind var rhs parameters 0
            theta <- lift $ var +-> makeNestedNLam n lhs
            modify (zonkLVar theta)
            return (theta <> subst)
    handleErr :: HopuFail -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err
    canView :: Labeling -> TermNode -> Bool
    canView labeling = go where
        go :: TermNode -> Bool
        go (NLam t1) = go t1
        go (NApp t1 t2) = go t1 && go t2
        go (NCon c) = lookupLabel var labeling >= lookupLabel c labeling
        go (LVar x) = lookupLabel var labeling >= lookupLabel x labeling

simplify :: [Disagreement] -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
simplify = flip loop mempty . zip (repeat 0) where
    loop :: [(Int, Disagreement)] -> LogicVarSubst -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
    loop [] subst labeling = return ([], HopuSol labeling subst)
    loop ((l, lhs :=?=: rhs) : disagreements) subst labeling = dispatch l (rewrite NF lhs) (rewrite NF rhs) where
        dispatch :: Int -> TermNode -> TermNode -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
        dispatch l lhs rhs
            | (lambda1, lhs') <- viewNestedNLam lhs
            , (lambda2, rhs') <- viewNestedNLam rhs
            , lambda1 > 0 && lambda2 > 0
            = (\lambda -> dispatch (l + lambda) (makeNestedNLam (lambda1 - lambda) lhs') (makeNestedNLam (lambda2 - lambda) rhs')) $! min lambda1 lambda2
            | (lambda1, lhs') <- viewNestedNLam lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , lambda1 > 0 && isRigidAtom rhs_head
            = dispatch (l + lambda1) lhs' (List.foldl' mkNApp (rewriteWithSusp rhs_head 0 lambda1 [] HNF) ([ mkSusp rhs_tail_element 0 lambda1 [] | rhs_tail_element <- rhs_tail ] ++ map mkNIdx [lambda1 - 1, lambda1 - 2 .. 0]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (lambda2, rhs') <- viewNestedNLam rhs
            , isRigidAtom lhs_head && lambda2 > 0
            = dispatch (l + lambda2) (List.foldl' mkNApp (rewriteWithSusp lhs_head 0 lambda2 [] HNF) ([ mkSusp lhs_tail_element 0 lambda2 [] | lhs_tail_element <- lhs_tail ] ++ map mkNIdx [lambda2 - 1, lambda2 - 2 .. 0])) rhs'
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
                output <- lift (mksubst var rhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (bindVars subst' disagreements) (subst' <> subst) labeling'
            | (LVar var, parameters) <- unfoldlNApp rhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst var lhs parameters labeling)
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
            return (bindVars subst' (makeNestedNLam l lhs :=?=: makeNestedNLam l rhs) : disagreements', HopuSol labeling' (subst' <> subst))

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
flatten (VarBinding mapsto) = go . rewrite NF where
    go :: TermNode -> TermNode
    go (LVar v) = maybe (mkLVar v) id (Map.lookup v mapsto)
    go (NCon c) = mkNCon c
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam t) = mkNLam (go t)

(+->) :: Monad m => LogicVar -> TermNode -> ExceptT HopuFail m VarBinding
v +-> t
    | LVar v == t' = return (VarBinding $! Map.empty)
    | v `Set.member` getLVars t' = throwE OccursCheckFail
    | otherwise = return (VarBinding $! Map.singleton v t')
    where
        t' :: TermNode
        t' = etaReduce (rewrite NF t)

getNewLVar :: MonadUnique m => IsTypeLevel -> ScopeLevel -> StateT Labeling m TermNode
getNewLVar is_ty label = do
    u <- getUnique
    let sym = if is_ty then LV_ty_var $! u else LV_Unique $! u
    sym `seq` modify (enrollLabel sym label)
    return (mkLVar sym)

etaReduce :: TermNode -> TermNode
etaReduce = go . rewrite NF where
    isFreeIn :: DeBruijn -> TermNode -> Bool
    isFreeIn i (NIdx j) = i == j
    isFreeIn i (NApp t1 t2) = isFreeIn i t1 || isFreeIn i t2
    isFreeIn i (NLam t1) = isFreeIn (i + 1) t1
    isFreeIn i _ = False
    decr :: TermNode -> TermNode
    decr (LVar x) = mkLVar x
    decr (NIdx i) = if i > 0 then mkNIdx (i - 1) else error "etaReduce.decr: unreachable..."
    decr (NCon c) = mkNCon c
    decr (NApp t1 t2) = mkNApp (decr t1) (decr t2)
    decr (NLam t1) = mkNLam (decr t1)
    go :: TermNode -> TermNode
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam t1) = case go t1 of
        NApp t1' (NIdx 0)
            | not (isFreeIn 0 t1') -> decr t1'
        t1' -> mkNLam t1'
    go t = t
