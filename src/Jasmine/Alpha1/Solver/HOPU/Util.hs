module Jasmine.Alpha1.Solver.HOPU.Util where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Z.Algo.Function
import Z.Utils

infix 9 :=?=:
infixr 8 <+>

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
    isFlatWRT :: a -> LVarSubst -> Bool

instance Flattable (TermNode) where
    isFlatWRT t sigma = getLVars t `Set.disjoint` Map.keysSet sigma

instance Flattable (Disagreement) where
    isFlatWRT (lhs :=?=: rhs) sigma = isFlatWRT lhs sigma && isFlatWRT rhs sigma

instance Flattable a => Flattable [a] where
    isFlatWRT xs sigma = all (\x -> isFlatWRT x sigma) xs

instance HasLVar (Disagreement) where
    getLVars (lhs :=?=: rhs) = Set.union (getLVars lhs) (getLVars rhs)
    substLVar sigma (lhs :=?=: rhs) = substLVar sigma lhs :=?=: substLVar sigma rhs

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (x `elem` xs) && areAllDistinct xs

makeMulitMap :: Ord k => [(k, a)] -> Map.Map k [a]
makeMulitMap = foldr (uncurry $ \k -> \x -> Map.alter (Just . maybe [x] (\xs -> x : xs)) k) Map.empty

bridge :: (a -> a -> b) -> [a] -> [b]
bridge op (x1 : x2 : xs) = op x1 x2 : bridge op (x2 : xs)
bridge _ _ = []

-- spec of (<+>): sigma = sigma2 <+> sigma1 -> substLVar sigma t = substLVar sigma2 (substLVar sigma1 t)
(<+>) :: LVarSubst -> LVarSubst -> LVarSubst
sigma2 <+> sigma1 = Map.map (substLVar sigma2) sigma1 `Map.union` sigma2

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

isRigid :: TermNode -> Bool
isRigid (NIdx i) = True
isRigid (NCon c) = True
isRigid (Prim prim_op) = not (prim_op == INTERRUPT || prim_op == WILD_CARD)
isRigid _ = False

isPatternWRT :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternWRT x params labeling = and
    [ all isRigid params
    , areAllDistinct params
    , and
        [ viewScope x labeling < viewScope c labeling
        | NCon c <- params
        ]
    ]
