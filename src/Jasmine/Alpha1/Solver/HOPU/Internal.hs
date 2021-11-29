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
    | Just x <- getLVar t1 = makeSubstitution (x, ts1) (unviewNApp t2 ts2)
    | Just x <- getLVar t2 = makeSubstitution (x, ts2) (unviewNApp t1 ts1)
    | otherwise = return [Delayed ByERR (unviewNApp t1 ts1) (unviewNApp t2 ts2)]

makeSubstitution :: GeneratingUniqueMonad m => (Unique, [TermNode]) -> TermNode -> StateT AtomEnv m [Problem]
makeSubstitution (fun, args) rhs
    | null args
    = makeSubstitutionFirstOrder fun rhs
    | (l, t2) <- viewNLam rhs
    , l > 0
    = makeSubstitution (fun, map (liftLam l) args ++ map mkNIdx [l - 1, l - 2 .. 0]) t2
    | (fun', params) <- viewNApp rhs
    , mkLVar fun == fun'
    = do
        env <- get
        if isPattern (logicvar fun) args env
            then do
                uni <- getNewUnique
                let n = length args - 1
                    ts = [ mkNIdx (n - i) | i <- [0, 1 .. n], args !! i == params !! i ]
                    t = mkLVar uni
                makeSubstitutionFirstOrder fun (unviewNLam (length args) (unviewNApp t ts))
            else return [Delayed ByNaP (unviewNApp (mkLVar fun) args) rhs]
    | otherwise
    = do
        env <- get
        if isPattern (logicvar fun) args env
            then do
                body <- bindsTo fun args rhs 0
                makeSubstitutionFirstOrder fun (unviewNLam (length args) body)
            else return [Delayed ByNaP (unviewNApp (mkLVar fun) args) rhs]

makeSubstitutionFirstOrder :: GeneratingUniqueMonad m => Unique -> TermNode -> StateT AtomEnv m [Problem]
makeSubstitutionFirstOrder var rhs
    | mkLVar var == rhs = return []
    | logicvar var `Set.member` collectAtoms rhs = return [Delayed OCCUR (mkLVar var) rhs]
    | otherwise = do
        env <- get
        put (Map.alter (Just . maybe (AtomInfo { _scope_lv = getNewScope env maxBound, _eval_ref = Just rhs, _type_ref = Nothing }) (\info -> info { _scope_lv = getNewScope env (_scope_lv info) })) var env)
        case Map.lookup var env of
            Nothing -> return []
            Just info -> simplify (maybe [] (\lhs -> [lhs :==: rhs]) (_eval_ref info))
    where
        getNewScope :: AtomEnv -> ScopeLevel -> ScopeLevel
        getNewScope env old_one = List.foldl' min old_one (map (getScopeLevel env) (Set.toAscList (collectAtoms rhs)))

bindsTo :: GeneratingUniqueMonad m => Unique -> [TermNode] -> TermNode -> SmallNat -> StateT AtomEnv m TermNode
bindsTo = undefined
