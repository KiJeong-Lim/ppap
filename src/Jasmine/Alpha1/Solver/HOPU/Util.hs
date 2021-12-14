module Jasmine.Alpha1.Solver.HOPU.Util where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Z.Algo.Function
import Z.Utils

infix 9 :=?=:

type HasSolvedAtLeastOneProblem = Bool

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Show)

data MkRefResult item
    = MkRefResult Labeling item
    | NotAPattern
    | SpecialPrim
    deriving (Show)

class Flat a where
    isFlatWrt :: a -> LVarSubst -> Bool

instance HasLVar (Disagreement) where
    getLVars (lhs :=?=: rhs) = getLVars lhs `Set.union` getLVars rhs
    substLVar sigma (lhs :=?=: rhs) = substLVar sigma lhs :=?=: substLVar sigma rhs

instance Flat (TermNode) where
    isFlatWrt t sigma = getLVars t `Set.disjoint` Map.keysSet sigma

instance Flat (Disagreement) where
    isFlatWrt (lhs :=?=: rhs) sigma = isFlatWrt lhs sigma && isFlatWrt rhs sigma

instance Flat a => Flat [a] where
    isFlatWrt = flip (all . flip isFlatWrt)

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (x `elem` xs) && areAllDistinct xs

makeMultiMap :: Ord k => [(k, a)] -> Map.Map k [a]
makeMultiMap = foldr (uncurry $ \k -> \x -> Map.alter (Just . maybe [x] (\xs -> x : xs)) k) Map.empty

mkBridges :: (a -> a -> b) -> [a] -> [b]
mkBridges bin_op (x1 : x2 : xs) = bin_op x1 x2 : mkBridges bin_op (x2 : xs)
mkBridges bin_op _ = []

makeNewScopeEnv :: LVarSubst -> Labeling -> Labeling 
makeNewScopeEnv sigma scope_env = Map.fromSet (\v -> viewScope v scope_env & (\v_scope -> List.foldl' min v_scope [ x_scope | (x, t) <- Map.toList sigma, v `Set.member` getLVars t, x_scope <- maybe [] pure (Map.lookup x scope_env) ])) (Map.keysSet sigma `Set.union` Map.keysSet scope_env)

liftLams :: SmallNat -> TermNode -> TermNode
liftLams l t = rewriteWithSusp t 0 l [] NF

isPrimCon :: Primitives -> Bool
isPrimCon (INTERRUPT) = False
isPrimCon (WILD_CARD) = False
isPrimCon _ = True

isRigid :: TermNode -> Bool
isRigid (NIdx i) = True
isRigid (NCon c) = True
isRigid (Prim prim_op) = isPrimCon prim_op
isRigid _ = False

dukeOfCon :: Labeling -> (ScopeLevel -> Bool) -> TermNode -> Bool
dukeOfCon scope_env cond (NCon c) = cond (viewScope c scope_env)
dukeOfCon scope_env cond (Prim prim_op) = cond (viewScope prim_op scope_env)
dukeOfCon scope_env cond _ = False

isPatternWrt :: (LogicVar, [TermNode]) -> Labeling -> Bool
(x, params) `isPatternWrt` scope_env = and
    [ all isRigid params
    , areAllDistinct params
    , all (not . dukeOfCon scope_env (\c_scope -> viewScope x scope_env >= c_scope)) params
    ]
