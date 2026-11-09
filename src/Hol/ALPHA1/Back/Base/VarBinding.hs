module Hol.ALPHA1.Back.Base.VarBinding where

import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

infix 1 +->

type LVarSubst = VarBinding

newtype VarBinding
    = VarBinding { unVarBinding :: Map.Map LogicVar TermNode }
    deriving (Eq)

class HasLVar expr where
    getFreeLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    applyBinding :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LVarSubst -> expr -> expr

instance HasLVar TermNode where
    getFreeLVars (LVar v) = Set.insert v
    getFreeLVars (NCon c) = id
    getFreeLVars (NIdx i) = id
    getFreeLVars (NApp t1 t2) = getFreeLVars t1 . getFreeLVars t2
    getFreeLVars (NAbs t) = getFreeLVars t
    getFreeLVars (Susp t ol nl env) = getFreeLVars (rewriteWithSusp t ol nl env HNF)
    applyBinding = flatten

instance HasLVar a => HasLVar [a] where
    getFreeLVars = flip (foldr getFreeLVars)
    applyBinding = map . applyBinding

instance HasLVar b => HasLVar (a, b) where
    getFreeLVars = getFreeLVars . snd
    applyBinding = fmap . applyBinding

instance HasLVar a => HasLVar (Map.Map k a) where
    getFreeLVars = getFreeLVars . Map.elems
    applyBinding = Map.map . applyBinding

instance Semigroup VarBinding where
    theta2 <> theta1
        | Map.null map2 = theta1
        | Map.null map1 = theta2
        | otherwise = map21 `seq` VarBinding map21
        where
            map1 :: Map.Map LogicVar TermNode
            map1 = unVarBinding theta1
            map2 :: Map.Map LogicVar TermNode
            map2 = unVarBinding theta2
            map21 :: Map.Map LogicVar TermNode
            map21 = applyBinding theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = map0 `seq` VarBinding map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

instance ZonkLVar VarBinding where
    zonkLVar subst binding = subst <> binding

instance ZonkLVar a => ZonkLVar [a] where
    zonkLVar = map . zonkLVar

getFreeLVs :: HasLVar expr => expr -> Set.Set LogicVar
getFreeLVs = flip getFreeLVars Set.empty

occursFreeIn :: LogicVar -> TermNode -> Bool
occursFreeIn v = go where
    go :: TermNode -> Bool
    go (LVar v') = v == v'
    go (NCon c) = False
    go (NIdx i) = False
    go (NApp t1 t2) = go t1 || go t2
    go (NAbs t) = go t
    go (Susp t ol nl env) = go (rewriteWithSusp t ol nl env HNF)

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding mapsto)
    | Map.null mapsto = id
    | otherwise = \t -> maybe t id (go t)
    where
        go :: TermNode -> Maybe TermNode
        go (LVar v) = Map.lookup v mapsto
        go (NCon c) = Nothing
        go (NIdx i) = Nothing
        go (NApp t1 t2) = case go t1 of
            Nothing -> case go t2 of
                Nothing -> Nothing
                Just t2' -> Just (mkNApp t1 t2')
            Just t1' -> Just (mkNApp t1' (maybe t2 id (go t2)))
        go (NAbs t) = fmap mkNAbs (go t)
        go (Susp t ol nl env) = case go t of
            Nothing -> case goEnv env of
                Nothing -> Nothing
                Just env' -> Just (mkSusp t ol nl env')
            Just t' -> Just (mkSusp t' ol nl (maybe env id (goEnv env)))
        goEnv :: SuspEnv -> Maybe SuspEnv
        goEnv [] = Nothing
        goEnv (item : items) = case goItem item of
            Nothing -> case goEnv items of
                Nothing -> Nothing
                Just items' -> Just (item : items')
            Just item' -> Just (item' : maybe items id (goEnv items))
        goItem :: SuspItem -> Maybe SuspItem
        goItem (Dummy l) = Nothing
        goItem (Binds t l) = fmap (\t' -> mkBinds t' l) (go t)

extendBinding :: LVarSubst -> VarBinding -> VarBinding
extendBinding (VarBinding new) (VarBinding old) = VarBinding (Map.union new old)

resolveBinding :: VarBinding -> TermNode -> TermNode
resolveBinding (VarBinding mapsto)
    | Map.null mapsto = id
    | otherwise = go
    where
        go :: TermNode -> TermNode
        go (LVar v) = maybe (mkLVar v) go (Map.lookup v mapsto)
        go (NCon c) = mkNCon c
        go (NIdx i) = mkNIdx i
        go (NApp t1 t2) = mkNApp (go t1) (go t2)
        go (NAbs t) = mkNAbs (go t)
        go (Susp t ol nl env) = mkSusp (go t) ol nl (lensForSuspEnv go env)

(+->) :: LogicVar -> TermNode -> Maybe VarBinding
v +-> t
    | LVar v == t' = return (VarBinding Map.empty)
    | v `occursFreeIn` t' = Nothing
    | otherwise = return (VarBinding (Map.singleton v t'))
    where
        t' :: TermNode
        t' = rewrite NF t
