module Jasmine.Alpha1.Header.Export
    -- Jasmine.Alpha1.Header.Util
    ( SrcRow, SrcCol, SrcPos, LargeId, SmallId, Keyword, ModName
    , SrcLoc (_BegPos, _EndPos), DataConstructor (..), TypeConstructor (..), ReduceOption (..), Unique, UniqueMakerT
    , HasSrcLoc (..), HasAnnotation (..), GeneratingUniqueMonad (..)
    , mkSrcLoc, runUniqueMakerT
    -- Jasmine.Alpha1.Header.TermNode
    , DeBruijn, SuspEnv, SmallNat, Nat_ol, Nat_nl, ScopeLevel, DoesRepresentType, LogicVar
    , Constructor (..), Primitives (..), TermNode (..)
    , Constructible (..)
    , viewDCon, viewTCon, fromPrim, viewPrim, mkLVar, mkNIdx, mkNApp, mkNLam
    -- Jasmine.Alpha1.Header.TermNode.DeBruijn
    , rewriteWithSusp, rewrite
    -- Jasmine.Alpha1.Header.TermNode.Render
    -- Jasmine.Alpha1.Header.Export
    , JasminePP, JasminePragma, AtomEnv, LVarSubst, Labeling
    , SymbolReference (..), ThreadState (..)
    , HasLVar (..), HasScope (..)
    , viewNApps, foldNApps, viewNLams, foldNLams
    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.TermNode.DeBruijn
import Jasmine.Alpha1.Header.TermNode.Render
import Jasmine.Alpha1.Header.Util
import Z.Algo.Function (recNat)
import Z.Utils (callWithStrictArg)

type JasminePP = String

type JasminePragma = String

type AtomEnv = Map.Map Unique SymbolReference

type LVarSubst = Map.Map LogicVar TermNode
-- spec of LVarSubst: Map.lookup x sigma /= Just x for any x :: LogicVar, sigma :: LVarSubst.

type Labeling = Map.Map Unique ScopeLevel

data SymbolReference
    = SymRef
        { myScopeLv :: !(ScopeLevel)
        , myEvalRef :: !(Maybe TermNode)
        }
    deriving (Show)

data ThreadState
    = ThreadState
        { myProcessId :: Unique
        , mySymbolEnv :: AtomEnv
        }
    deriving (Show)

class HasLVar expr where
    getLVars :: expr -> Set.Set LogicVar
    substLVar :: LVarSubst -> expr -> expr

class HasScope a where
    viewScope :: a -> Labeling -> ScopeLevel

instance HasLVar (TermNode) where
    getLVars = flip accLVars Set.empty
    substLVar ctx = go where
        go :: TermNode -> TermNode
        go t = case t of
            LVar x -> maybe t id (Map.lookup x ctx)
            NApp t1 t2 -> mkNApp (go t1) (go t2)
            NLam t1 -> mkNLam (go t1)
            NFix t1 -> NFix $! go t1
            Susp t ol nl env -> mkSusp (go t) ol nl (map (lensForSusp go) env)
            t -> t

instance HasLVar a => HasLVar [a] where
    getLVars = Set.unions . map getLVars
    substLVar = map . substLVar

instance HasLVar b => HasLVar (a, b) where
    getLVars = getLVars . snd
    substLVar = fmap . substLVar

instance HasScope (Unique) where
    viewScope v = maybe maxBound id . Map.lookup v

instance HasScope (DataConstructor) where
    viewScope (DC_Unique c) = maybe 0 id . Map.lookup c
    viewScope dc = const 0

instance HasScope (TypeConstructor) where
    viewScope (TC_Atom c) = maybe 0 id . Map.lookup c
    viewScope tc = const 0

instance HasScope (Constructor) where
    viewScope (DataConstr dc) = viewScope dc
    viewScope (TypeConstr tc) = viewScope tc

instance HasScope (Primitives) where
    viewScope (WILD_CARD) = const maxBound
    viewScope (INTERRUPT) = const maxBound
    viewScope prim_op = const 0

instance HasScope (TermNode) where
    viewScope (LVar x) = viewScope x
    viewScope (NCon c) = viewScope c
    viewScope (Prim prim_op) = viewScope prim_op
    viewScope _ = const (negate 1)

viewNApps :: TermNode -> (TermNode, [TermNode])
viewNApps = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

foldNApps :: (TermNode, [TermNode]) -> TermNode
foldNApps = uncurry (List.foldl' mkNApp)

viewNLams :: TermNode -> (SmallNat, TermNode)
viewNLams = go 0 where
    go :: SmallNat -> TermNode -> (SmallNat, TermNode)
    go l (NLam t1) = go (succ l) t1
    go l t = l `seq` (l, t)

foldNLams :: (SmallNat, TermNode) -> TermNode
foldNLams (l, t) = recNat t (const mkNLam) l

accLVars :: TermNode -> Set.Set LogicVar -> Set.Set LogicVar
accLVars (LVar x) = Set.insert x
accLVars (NApp t1 t2) = accLVars t1 . accLVars t2
accLVars (NLam t1) = accLVars t1
accLVars (NFix t1) = accLVars t1
accLVars (Susp t ol nl env) = accLVars (rewriteWithSusp t ol nl env NF)
accLVars _ = id
