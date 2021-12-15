module Jasmine.Alpha1.Solver.HOPU.Internal where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Jasmine.Alpha1.Solver.HOPU.Util
import Z.Algo.Function
import Z.Utils

updateAtomEnvNaively :: (Labeling, LVarSubst) -> AtomEnv -> AtomEnv
updateAtomEnvNaively (scope_env, sigma) ctx = Map.mapWithKey (\v -> \v_scope -> SymRef { myScopeLv = v_scope, myEvalRef = takeFirstOf id [substLVar sigma <$> Map.lookup v (Map.mapMaybe myEvalRef ctx), Map.lookup v sigma] }) scope_env

callSimpleHopuSolver :: GeneratingUniqueMonad m => [(TermNode, TermNode)] -> Labeling -> m (Maybe ([(TermNode, TermNode)], (Labeling, LVarSubst)))
callSimpleHopuSolver = entryOfSimpleHopuSolver where
    entryOfSimpleHopuSolver :: GeneratingUniqueMonad m => [(TermNode, TermNode)] -> Labeling -> m (Maybe ([(TermNode, TermNode)], (Labeling, LVarSubst)))
    entryOfSimpleHopuSolver probs scope_env = runMaybeT (execMainRoutine (map (uncurry (:=?=:)) probs) (scope_env, Map.empty) >>= uncurry (\new_probs -> \hopu_sol -> return ([ (lhs, rhs) | lhs :=?=: rhs <- new_probs ], hopu_sol)))
    execMainRoutine :: GeneratingUniqueMonad m => [Disagreement] -> (Labeling, LVarSubst) -> MaybeT m ([Disagreement], (Labeling, LVarSubst))
    execMainRoutine probs env
        | null probs = return (probs, env)
        | otherwise = do
            let scope_env = fst env
                lvar_subst = snd env
            ((delayed_probs, (fresh_scope_env, fresh_lvar_binding)), has_changed) <- runStateT (entryOfSimpleHopu probs scope_env) False
            let multi_map = Map.unionWith (++) (Map.map pure lvar_subst) (makeMultiMap fresh_lvar_binding)
                conflicts = Map.elems multi_map >>= mkBridges (:=?=:)
                fresh_lvar_subst = Map.withoutKeys multi_map (Map.keysSet lvar_subst) & Map.map head
                new_probs = substLVar fresh_lvar_subst (conflicts ++ delayed_probs)
                new_env = (makeNewScopeEnv fresh_lvar_subst fresh_scope_env, fresh_lvar_subst `compose` lvar_subst)
            if has_changed then execMainRoutine new_probs new_env else return (new_probs, new_env)
    compose :: LVarSubst -> LVarSubst -> LVarSubst
    sigma_new `compose` sigma_old = Map.map (substLVar sigma_new) sigma_old `Map.union` sigma_new

entryOfSimpleHopu :: GeneratingUniqueMonad m => [Disagreement] -> Labeling -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
entryOfSimpleHopu = simplify where
    simplify :: GeneratingUniqueMonad m => [Disagreement] -> Labeling -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
    simplify [] scope_env = return ([], (scope_env, []))
    simplify (lhs :=?=: rhs : probs) scope_env_0 = do
        (delayed_probs_1, (scope_env_1, lvar_binding_1)) <- simplify1 0 (rewrite NF lhs) (rewrite NF rhs) scope_env_0
        (delayed_probs_2, (scope_env_2, lvar_binding_2)) <- simplify probs scope_env_1
        return (delayed_probs_1 ++ delayed_probs_2, (scope_env_2, lvar_binding_1 ++ lvar_binding_2))
    simplify1 :: GeneratingUniqueMonad m => SmallNat -> TermNode -> TermNode -> Labeling -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
    simplify1 lambda lhs rhs scope_env
        | (l1, lhs') <- viewNLams lhs
        , (l2, rhs') <- viewNLams rhs
        , l1 > 0 && l2 > 0
        = min l1 l2 & (\l -> simplify1 (lambda + l) (foldNLams (l1 - l, lhs')) (foldNLams (l2 - l, rhs')) scope_env) 
        | (l1, lhs') <- viewNLams lhs
        , (rhs_hd, rhs_tl) <- viewNApps rhs
        , l1 > 0 && isRigid rhs_hd
        = simplify1 (lambda + l1) lhs' (foldNApps (liftLams l1 rhs_hd, map (liftLams l1) rhs_tl)) scope_env
        | (lhs_hd, lhs_tl) <- viewNApps lhs
        , (l2, rhs') <- viewNLams rhs
        , l2 > 0 && isRigid lhs_hd
        = simplify1 (lambda + l2) (foldNApps (liftLams l2 lhs_hd, map (liftLams l2) lhs_tl)) rhs' scope_env
        | lhs == rhs
        = return ([], (scope_env, []))
        | (lhs_hd, lhs_tl) <- viewNApps lhs
        , (rhs_hd, rhs_tl) <- viewNApps rhs
        , isRigid lhs_hd && isRigid rhs_hd
        = if lhs_hd == rhs_hd && length lhs_tl == length rhs_tl
            then simplify [ foldNLams (lambda, t1) :=?=: foldNLams (lambda, t2) | (t1, t2) <- zip lhs_tl rhs_tl ] scope_env
            else fail "unifying-failed: case=RigidRigid, cause=head-not-matched-or-args-length-not-matched"
        | (LVar x, x_args) <- viewNApps lhs
        = if (x, x_args) `isPatternWrt` scope_env
            then calcLVarBinding x x_args rhs
            else delayBy NotAPattern
        | (LVar x, x_args) <- viewNApps rhs
        = if (x, x_args) `isPatternWrt` scope_env
            then calcLVarBinding x x_args lhs
            else delayBy NotAPattern
        | otherwise
        = delayBy SpecialPrim
        where
            calcLVarBinding :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
            calcLVarBinding x x_args x_eval_ref = do
                res <- lift $ runExceptT (entryOfSimpleMkRef x x_args x_eval_ref scope_env)
                case res of
                    Left cause_to_defer -> delayBy cause_to_defer
                    Right good_res -> do
                        put True
                        return ([], good_res)
            delayBy :: Monad m => MkRefFailed -> m ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
            delayBy cause_to_defer = return ([foldNLams (lambda, lhs) :=?=: foldNLams (lambda, rhs)], (scope_env, []))

entryOfSimpleMkRef :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> Labeling -> ExceptT MkRefFailed (MaybeT m) (Labeling, [(LogicVar, TermNode)])
entryOfSimpleMkRef = toplevelctrl where
    toplevelctrl :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> Labeling -> ExceptT MkRefFailed (MaybeT m) (Labeling, [(LogicVar, TermNode)])
    toplevelctrl x x_args rhs scope_env
        | (l', rhs') <- viewNLams rhs
        , (LVar x', rhs_args) <- viewNApps rhs'
        , x == x'
        = do
            let n = length rhs_args
                lhs_args = map (liftLams l') x_args ++ map mkNIdx [l' - 1, l' - 2 .. 0]
            if l + l' == n
                then if (x', rhs_args) `isPatternWrt` scope_env
                    then do
                        h <- getNewUnique
                        let refined_rhs = foldNLams (n, foldNApps (mkLVar h, [ mkNIdx (n - 1 - i) | i <- [0, 1 .. n - 1], lhs_args !! i == rhs_args !! i ]))
                        return (Map.insert h (viewScope x scope_env) scope_env, [(x, refined_rhs)])
                    else throwE NotAPattern
                else fail "unifying-failed: case=ReflexiveFlex, cause=length-not-matched"
        | otherwise
        = do
            (refined_rhs, (new_scope_env, lvar_binding)) <- bindsLVarToRefinedEvalRef x x_args 0 rhs (scope_env, [])
            return (new_scope_env, (x, foldNLams (l, refined_rhs)) : lvar_binding) -- FIXED: refined_rhs --> foldNLams (l, refined_rhs)
        where
            l :: SmallNat
            l = length x_args
    bindsLVarToRefinedEvalRef :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> SmallNat -> TermNode -> (Labeling, [(LogicVar, TermNode)]) -> ExceptT MkRefFailed (MaybeT m) (TermNode, (Labeling, [(LogicVar, TermNode)]))
    bindsLVarToRefinedEvalRef x x_args l rhs (scope_env, lvar_binding_acc)
        | (l', rhs') <- viewNLams rhs
        , l' > 0
        = do
            (refined_rhs', (scope_env', lvar_binding_acc')) <- bindsLVarToRefinedEvalRef x x_args (l + l') rhs' (scope_env, lvar_binding_acc)
            return (foldNLams (l', refined_rhs'), (scope_env', lvar_binding_acc'))
        | (rhs_hd, rhs_tl) <- viewNApps rhs
        , isRigid rhs_hd
        = do
            refined_rhs_hd <- case rhs_hd of
                NIdx i -> case down1 rhs_hd (map (liftLams l) x_args ++ map mkNIdx [l - 1, l - 2 .. 0]) of
                    Just r -> return r
                    _ -> fail "unifying-failed: case=FlexRigid, cause=imitation-failed"
                r -> if dukeOfCon scope_env (\r_scope -> viewScope x scope_env >= r_scope) r
                    then return r
                    else fail "unifying-failed: case=FlexRigid, cause=imitation-failed"
            (refined_rhs_tl, (scope_env', lvar_binding_acc')) <- runStateT (mapM (StateT . bindsLVarToRefinedEvalRef x x_args l) rhs_tl) (scope_env, lvar_binding_acc)
            return (foldNApps (refined_rhs_hd, refined_rhs_tl), (scope_env', lvar_binding_acc'))
        | (LVar y, rhs_args) <- viewNApps rhs
        = if x == y
            then fail "unifying-failed: case=FlexFlex, cause=occurs-check-failed"
            else do
                let lhs_args = map (liftLams l) x_args ++ map mkNIdx [l - 1, l - 2 .. 0]
                    com_args = Set.toList (Set.fromList lhs_args `Set.intersection` Set.fromList rhs_args)
                    x_scope = viewScope x scope_env
                    y_scope = viewScope y scope_env
                    x_outer = com_args `down` lhs_args
                    y_outer = com_args `down` rhs_args
                if (y, rhs_args) `isPatternWrt` scope_env
                    then do
                        h <- getNewUnique
                        -- FIXED: (Map.insert h (min x_scope y_scope) scope_env) --> (Map.insert h x_scope scope_env)
                        let makeFlexFlexSolution x_inner y_inner = (foldNApps (mkLVar h, x_inner ++ x_outer), (Map.insert h x_scope scope_env, (y, foldNLams (length rhs_args, foldNApps (mkLVar h, y_inner ++ y_outer))) : lvar_binding_acc))
                        if x_scope < y_scope
                            then do
                                y_inner <- runReaderT (lhs_args `up` y) scope_env
                                let x_inner = y_inner `down` lhs_args
                                return (makeFlexFlexSolution x_inner y_inner)
                            else do
                                x_inner <- runReaderT (rhs_args `up` x) scope_env
                                let y_inner = x_inner `down` rhs_args
                                return (makeFlexFlexSolution x_inner y_inner)
                    else throwE NotAPattern
        | otherwise
        = throwE SpecialPrim
    down1 :: TermNode -> [TermNode] -> Maybe TermNode
    down1 arg args = fmap (\i -> mkNIdx (length args - 1 - i)) (arg `List.elemIndex` args)
    down :: [TermNode] -> [TermNode] -> [TermNode]
    subset_of_args `down` args = map (fromJust . flip down1 args) subset_of_args
    up :: Monad m => [TermNode] -> LogicVar -> ReaderT Labeling m [TermNode]
    cs `up` x = ask >>= \scope_env -> return (filter (dukeOfCon scope_env (\c_scope -> viewScope x scope_env >= c_scope)) cs)
