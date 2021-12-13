module Jasmine.Alpha1.Solver.HOPU.Util where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
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

class Flattable a where
    isFlatWrt :: a -> LVarSubst -> Bool

instance Flattable (TermNode) where
    isFlatWrt t sigma = getLVars t `Set.disjoint` Map.keysSet sigma

instance Flattable (Disagreement) where
    isFlatWrt (lhs :=?=: rhs) sigma = isFlatWrt lhs sigma && isFlatWrt rhs sigma

instance Flattable a => Flattable [a] where
    isFlatWrt xs sigma = all (\x -> isFlatWrt x sigma) xs

instance HasLVar (Disagreement) where
    getLVars (lhs :=?=: rhs) = Set.union (getLVars lhs) (getLVars rhs)
    substLVar sigma (lhs :=?=: rhs) = substLVar sigma lhs :=?=: substLVar sigma rhs

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (x `elem` xs) && areAllDistinct xs

makeMulitMap :: Ord k => [(k, a)] -> Map.Map k [a]
makeMulitMap = foldr (uncurry $ \k -> \x -> Map.alter (Just . maybe [x] (\xs -> x : xs)) k) Map.empty

bridge :: (a -> a -> b) -> [a] -> [b]
bridge bin_op (x1 : x2 : xs) = bin_op x1 x2 : bridge bin_op (x2 : xs)
bridge bin_op _ = []

makeNewScopeEnv :: LVarSubst -> Labeling -> Labeling 
makeNewScopeEnv sigma labelings_old = Map.fromAscList labelings where
    labelings :: [(Unique, ScopeLevel)]
    labelings = do
        v <- Set.toAscList (Map.keysSet sigma `Set.union` Map.keysSet labelings_old)
        let v_scope = viewScope v labelings_old
        return
            ( v
            , List.foldl' min v_scope
                [ u_scope
                | (u, t) <- Map.toList sigma
                , v `Set.member` getLVars t
                , u_scope <- maybe [] pure (Map.lookup u labelings_old)
                ]
            )

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
