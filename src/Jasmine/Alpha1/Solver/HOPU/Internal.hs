module Jasmine.Alpha1.Solver.HOPU.Internal where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Jasmine.Alpha1.Solver.HOPU.Util
import Z.Algo.Function
import Z.Utils

updateAtomEnv :: (AtomNode, TermNode) -> AtomEnv -> AtomEnv
updateAtomEnv = undefined

simplify :: GeneratingUniqueMonad m => [Problem] -> StateT AtomEnv m [Problem]
simplify [] = return []
simplify ((lhs :==: rhs) : probs) = do
    env <- get
    new_probs <- simplifyUnificationProblemOnce (flatten env lhs) (flatten env rhs)
    simplify (new_probs ++ probs)
simplify (prob : probs) = do
    new_probs <- simplify probs
    return (prob : new_probs)

simplifyUnificationProblemOnce :: GeneratingUniqueMonad m => TermNode -> TermNode -> StateT AtomEnv m [Problem]
simplifyUnificationProblemOnce lhs rhs
    | (l1, t1) <- viewNLam lhs
    , (l2, t2) <- viewNLam rhs
    , l1 > 0 && l2 > 0
    = case l1 `compare` l2 of
        LT -> simplifyUnificationProblemOnce t1 (unviewNLam (l2 - l1) t2)
        EQ -> simplifyUnificationProblemOnce t1 t2
        GT -> simplifyUnificationProblemOnce (unviewNLam (l1 - l2) t1) t2
    | (t1, ts1) <- viewNApp lhs
    , (l2, t2) <- viewNLam rhs
    , l2 > 0
    = simplifyUnificationProblemOnce (unviewNApp (liftLam l2 t1) (map (liftLam l2) ts1 ++ map mkNIdx [l2 - 1, l2 - 2 .. 0])) t2
    | (l1, t1) <- viewNLam lhs
    , (t2, ts2) <- viewNApp rhs
    , l1 > 0
    = simplifyUnificationProblemOnce t1 (unviewNApp (liftLam l1 t2) (map (liftLam l1) ts2 ++ map mkNIdx [l1 - 1, l1 - 2 .. 0]))
    | otherwise
    = simplifyUnificationProblemNApp (viewNApp lhs) (viewNApp rhs)

simplifyUnificationProblemNApp :: GeneratingUniqueMonad m => (TermNode, [TermNode]) -> (TermNode, [TermNode]) -> StateT AtomEnv m [Problem]
simplifyUnificationProblemNApp (t1, ts1) (t2, ts2)
    | t1 == fromPrim TmWcard = return []
    | t2 == fromPrim TmWcard = return []
    | t1 == fromPrim SPY = return [Delayed BySpy (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t2 == fromPrim SPY = return [Delayed BySpy (unviewNApp t2 ts2) (unviewNApp t1 ts1)]
    | isRigid t1 && isRigid t2
    = if t1 == t2 && length ts1 == length ts2
        then simplify (zipWith (:==:) ts1 ts2)
        else return [Delayed ByRew (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t1 == fromPrim TmGuard = return [Delayed GUARD (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t2 == fromPrim TmGuard = return [Delayed GUARD (unviewNApp t2 ts2) (unviewNApp t1 ts1)]
    | Just x <- getLVar t1 = makeSubstitution x ts1 (unviewNApp t2 ts2)
    | Just x <- getLVar t2 = makeSubstitution x ts2 (unviewNApp t1 ts1)
    | otherwise = return [Delayed ByERR (unviewNApp t1 ts1) (unviewNApp t2 ts2)]

makeSubstitution :: GeneratingUniqueMonad m => Unique -> [TermNode] -> TermNode -> StateT AtomEnv m [Problem]
makeSubstitution = undefined
