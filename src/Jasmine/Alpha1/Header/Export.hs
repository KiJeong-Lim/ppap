module Jasmine.Alpha1.Header.Export
    -- Jasmine.Alpha1.Header.Util
    ( SrcRow, SrcCol, SrcPos, LargeId, SmallId, Keyword, ModName
    , SrcLoc (_BegPos, _EndPos), DataConstructor, TypeConstructor, ReduceOption (..), Unique, UniqueMakerT
    , HasSrcLoc (..), HasAnnotation (..), GeneratingUniqueMonad (..)
    , mkSrcLoc, runUniqueMakerT
    -- Jasmine.Alpha1.Header.TermNode
    , DeBruijn, SuspEnv, Nat_ol, Nat_nl, ScopeLevel, DoesRepresentType
    , LogicVar (..), Constructor (..), Primitives (..), TermNode (..)
    , Constructible (..)
    , flexTVar, flexIVar, viewFlex, viewDCon, viewTCon, fromPrim, viewPrim, mkLVar, mkNIdx, mkNApp, mkNLam
    -- Jasmine.Alpha1.Header.TermNode.DeBruijn
    , rewriteWithSusp, rewrite
    -- Jasmine.Alpha1.Header.TermNode.Render
    -- Jasmine.Alpha1.Header.Export
    , JasminePP, JasminePragma, AtomEnv
    , SymbolReference (..), ThreadState (..)
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

data SymbolReference
    = SymRef
        { myScopeLv :: ScopeLevel
        , myEvalRef :: Maybe TermNode
        }
    deriving (Show)

data ThreadState
    = ThreadState
        { myProcessId :: Unique
        , mySymbolEnv :: AtomEnv
        }
    deriving (Show)

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

foldNLams :: SmallNat -> TermNode -> TermNode
foldNLams l t = recNat t (const mkNLam) l
