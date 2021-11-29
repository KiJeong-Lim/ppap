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
    , ScopeLevel
    , AtomEnv
    , SmallNat
    , AtomInfo (..)
    , mkLVar
    , mkNCon
    , unviewNLam
    , unviewNApp
    , viewNLam
    , viewNApp
    , liftLam
    , flatten
    , collectUniqs
    , logicvar
    , constructor
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

type ScopeLevel = SmallNat

data AtomInfo
    = AtomInfo
        { _type_ref :: Maybe TermNode
        , _eval_ref :: Maybe TermNode
        , _scope_lv :: ScopeLevel
        }
    deriving (Show)

mkLVar :: Unique -> TermNode
mkLVar = callWithStrictArg (Atom . logicvar)

mkNCon :: Unique -> TermNode
mkNCon = callWithStrictArg (Atom . constructor)

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
flatten env = rewrite NF . go where
    go :: TermNode -> TermNode
    go (Atom a) = flattenAtom a
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam t1) = mkNLam (go t1)
    go (Susp t ol nl env) = go (rewriteWithSusp t ol nl env NF)
    flattenAtom :: AtomNode -> TermNode
    flattenAtom a = case a of
        Uniq is_constr uni -> case Map.lookup uni env >>= _eval_ref of
            Nothing -> mkAtom a
            Just t -> flatten (Map.delete uni env) t
        _ -> mkAtom a

collectUniqs :: TermNode -> Set.Set Unique
collectUniqs = flip go Set.empty where
    fromAtom :: AtomNode -> Set.Set Unique -> Set.Set Unique
    fromAtom (Uniq _ uni) = Set.insert uni
    fromAtom _ = id
    go :: TermNode -> Set.Set Unique -> Set.Set Unique
    go (Atom x) = fromAtom x
    go (NIdx i) = id
    go (NApp t1 t2) = go t1 . go t2
    go (NLam t1) = go t1
    go (Susp t ol nl env) = go (rewriteWithSusp t ol nl env NF)

logicvar :: Unique -> AtomNode
logicvar = Uniq False

constructor :: Unique -> AtomNode
constructor = Uniq True
