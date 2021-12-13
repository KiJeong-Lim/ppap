module Jasmine.Alpha1.Solver.HOPU where

import Control.Monad.Trans.State.Strict
import Jasmine.Alpha1.Header.Export
import Jasmine.Alpha1.Solver.HOPU.Internal

{-
-- Invariants: (probs_fin, env_fin) <- callHopuSolver probs_init env_init
-- 1. If isFlatWRT probs_init env_init, then isFlatWRT probs_fin env_fin.
execCoreHopuSolver :: GeneratingUniqueMonad m => [Disagreement] -> AtomEnv -> MaybeT m ([Disagreement], AtomEnv)
execCoreHopuSolver = entryOfCoreHopuSolverExecutor where
    entryOfCoreHopuSolverExecutor :: GeneratingUniqueMonad m => [Disagreement] -> AtomEnv -> MaybeT m ([Disagreement], AtomEnv)
    entryOfCoreHopuSolverExecutor probs_init env_init = do
        -- Assumes:
        -- 1. isFlatWRT probs_init (Map.mapMaybe myEvalRef env_init)
        let scope_init = Map.map myScopeLv env_init
        (new_probs, (scope_fin, lvar_subst)) <- callCoreHopuSolver probs_init scope_init
        -- Guarantees:
        -- 2. Map.keysSet scope_init `Set.isSubsetOf` Map.keysSet scope_fin
        -- 3. areAllDistinct (map fst lvar_subst)
        -- 4. Set.fromList (map fst lvar_subst) `Set.disjoint` Map.mapMaybe myEvalRef env_init
        return
            ( new_probs -- =: probs_fin
            , Map.fromAscList -- =: env_fin
                [ (v, SymRef { myScopeLv = v_scope, myEvalRef = msum [Map.lookup v lvar_subst, Map.lookup v (Map.mapMaybe myEvalRef env_init)] })
                | (v, v_scope) <- Map.toAscList scope_fin
                ]
            )
        -- Guarantees:
        -- 5. isFlatWRT probs_fin env_fin
-}
