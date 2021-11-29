module Jasmine.Alpha1.Solver.HOPU.Util where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Z.Algo.Function
import Z.Utils

data Cause
    = ByRew
    | BySpy
    | GUARD
    | ByERR
    | OCCUR
    | ByNaP
    deriving (Eq, Ord, Show)

data Problem
    = TermNode :==: TermNode
    | Delayed Cause TermNode TermNode
    deriving (Eq, Ord, Show)

isConstr :: AtomNode -> Bool
isConstr (Uniq is_constr _) = is_constr
isConstr (Prim pr) = pr /= TmWcard && pr /= SPY

isRigid :: TermNode -> Bool
isRigid (Atom a) = isConstr a
isRigid (NIdx i) = True
isRigid (NApp t1 t2) = isRigid t1
isRigid (NLam t1) = isRigid t1
isRigid (Susp t ol nl env) = isRigid (rewriteWithSusp t ol nl env ALPHA)

getLVar :: TermNode -> Maybe Unique
getLVar (Atom (Uniq False x)) = Just x
getLVar _ = Nothing

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (x `elem` xs) && areAllDistinct xs

isPattern :: AtomNode -> [TermNode] -> AtomEnv -> Bool
isPattern v ts env = and
    [ all isRigid ts
    , areAllDistinct ts
    , and [ getScopeLevel env v < getScopeLevel env c | Atom c <- ts ]
    ]
