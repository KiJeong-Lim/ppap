module Jasmine.Alpha1.Header.Export
    -- Jasmine.Alpha1.Header.Util
    ( SrcRow
    , SrcCol
    , SrcPos
    , LargeId
    , SmallId
    , Keyword
    , ModName
    , SrcLoc (_BegPos, _EndPos)
    , LambdaTerm (..)
    , ReduceOption (..)
    , Unique (asInteger)
    , UniqueMakerT
    , HasSrcLoc (..)
    , HasAnnotation (..)
    , GeneratingUniqueMonad (..)
    , mkSrcLoc
    , runUniqueMakerT
    , getFVsOfLambdaTerm
    , substituteLambdaTerm
    , evalLambdaTerm
    , readLambdaTerm
    -- Jasmine.Alpha1.Header.TermNode
    , DeBruijn
    , SuspEnv
    , Nat_ol
    , Nat_nl
    , Primitives (..)
    , AtomNode (..)
    , TermNode (..)
    , SuspItem (..)
    , fromPrim
    , mkNatL
    , mkChrL
    , mkNIdx
    , mkNApp
    , mkNLam
    , mkAtom
    , mkSusp
    , mkBinds
    , mkDummy
    -- Jasmine.Alpha1.Header.TermNode.Util
    , rewriteWithSusp
    , rewrite
    , lensForSuspEnv
    , fromLambdaTermMakeTermNode
    -- Jasmine.Alpha1.Header.Export
    , JasminePP
    , JasminePragma
    , AtomEnv
    , AtomInfo (..)
    , mkLVar
    , mkNCon
    , unviewNLam
    , unviewNApp
    , viewNLam
    , viewNApp
    , liftLam
    , flatten
    , getScopeLevel
    ) where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.TermNode.Show
import Jasmine.Alpha1.Header.TermNode.Util
import Jasmine.Alpha1.Header.Util
import Z.Algo.Function (recNat)
import Z.Utils (callWithStrictArg)

type JasminePP = String

type JasminePragma = String

type AtomEnv = Map.Map Unique AtomInfo

data AtomInfo
    = AtomInfo
        { _type_ref :: Maybe TermNode
        , _eval_ref :: Maybe TermNode
        , _scope_lv :: SmallNat
        }
    deriving (Show)

mkLVar :: Unique -> TermNode
mkLVar = callWithStrictArg (Atom . Uniq False)

mkNCon :: Unique -> TermNode
mkNCon = callWithStrictArg (Atom . Uniq True)

unviewNLam :: SmallNat -> TermNode -> TermNode
unviewNLam nl t = recNat t (const mkNLam) nl

unviewNApp :: TermNode -> [TermNode] -> TermNode
unviewNApp = List.foldl' mkNApp

viewNLam :: TermNode -> (SmallNat, TermNode)
viewNLam = go 0 where
    go :: SmallNat -> TermNode -> (SmallNat, TermNode)
    go nl (NLam t1) = go (succ nl) t1
    go nl t = nl `seq` (nl, t)

viewNApp :: TermNode -> (TermNode, [TermNode])
viewNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (Atom (Prim (TmNatLit n))) ts = if n > 0 then (fromPrim TmSucc, mkNatL (pred n) : ts) else (mkNatL 0, ts)
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

liftLam :: SmallNat -> TermNode -> TermNode
liftLam l t = rewriteWithSusp t 0 l [] NF

flatten :: AtomEnv -> TermNode -> TermNode
flatten env = go . rewrite NF where
    go :: TermNode -> TermNode
    go (Atom a) = flattenAtom a
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam t1) = mkNLam (go t1)
    flattenAtom :: AtomNode -> TermNode
    flattenAtom a = case a of
        Uniq is_constr uni -> case Map.lookup uni env >>= _eval_ref of
            Nothing -> mkAtom a
            Just t -> flatten (Map.delete uni env) t
        _ -> mkAtom a

collectAtoms :: TermNode -> Set.Set AtomNode
collectAtoms (Atom x) = Set.singleton x
collectAtoms (NIdx i) = Set.empty
collectAtoms (NApp t1 t2) = Set.union (collectAtoms t1) (collectAtoms t2)
collectAtoms (NLam t1) = collectAtoms t1
collectAtoms (Susp t ol nl env) = collectAtoms (rewriteWithSusp t ol nl env NF)

getScopeLevel :: AtomEnv -> AtomNode -> SmallNat
getScopeLevel env (Prim pr) = 0
getScopeLevel env (Uniq is_constr uni) = maybe maxBound _scope_lv (Map.lookup uni env)
