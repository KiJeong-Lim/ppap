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

callCoreHopuSolver :: GeneratingUniqueMonad m => [Disagreement] -> Labeling -> m (Maybe ([Disagreement], (Labeling, LVarSubst)))
callCoreHopuSolver = entryOfCoreHopuSolver where
    entryOfCoreHopuSolver :: GeneratingUniqueMonad m => [Disagreement] -> Labeling -> m (Maybe ([Disagreement], (Labeling, LVarSubst)))
    entryOfCoreHopuSolver probs scope_env = runMaybeT (execMainRoutine probs (scope_env, Map.empty))
    execMainRoutine :: GeneratingUniqueMonad m => [Disagreement] -> (Labeling, LVarSubst) -> MaybeT m ([Disagreement], (Labeling, LVarSubst))
    execMainRoutine probs env
        | null probs = return (probs, env)
        | otherwise = do
            let scope_env = fst env
                lvar_subst = snd env
            ((delayed_probs, (fresh_scope_env, fresh_lvar_bindings)), has_changed) <- runStateT (entryOfSimpleHopu probs scope_env) False
            let multi_map = Map.unionWith (++) (Map.map pure lvar_subst) (makeMultiMap fresh_lvar_bindings)
                conflicts = Map.elems multi_map >>= mkBridges (:=?=:)
                fresh_lvar_subst = Map.fromAscList [ (x, head (multi_map Map.! x)) | (x, t) <- Map.toAscList multi_map, not (x `Set.member` Map.keysSet lvar_subst) ]
                new_probs = substLVar fresh_lvar_subst (conflicts ++ delayed_probs)
                new_env = (makeNewScopeEnv fresh_lvar_subst fresh_scope_env, fresh_lvar_subst `compose` lvar_subst)
            if has_changed
                then execMainRoutine new_probs new_env
                else return (new_probs, new_env)
    -- spec of compose: sigma = sigma2 `compose` sigma1 -> substLVar sigma t = substLVar sigma2 (substLVar sigma1 t)
    compose :: LVarSubst -> LVarSubst -> LVarSubst
    sigma_new `compose` sigma_old = Map.map (substLVar sigma_new) sigma_old `Map.union` sigma_new

entryOfSimpleHopu :: GeneratingUniqueMonad m => [Disagreement] -> Labeling -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
entryOfSimpleHopu = simplify . zip (repeat 0) where
    simplify :: GeneratingUniqueMonad m => [(SmallNat, Disagreement)] -> Labeling -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
    simplify [] scope_env = return ([], (scope_env, []))
    simplify ((l, lhs :=?=: rhs) : probs) scope_env_0 = do
        (delayed_probs_1, (scope_env_1, lvar_bindings_1)) <- simplify1 l (rewrite NF lhs) (rewrite NF rhs) scope_env_0
        -- Is it equiv to (simplify1 0 (rewrite NF (foldNLams (l, lhs))) (rewrite NF (foldNLams (l, rhs))) scope_env_0)?
        (delayed_probs_2, (scope_env_2, lvar_bindings_2)) <- simplify probs scope_env_1
        return (delayed_probs_1 ++ delayed_probs_2, (scope_env_2, lvar_bindings_1 ++ lvar_bindings_2))
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
            then simplify [ (lambda, lhs' :=?=: rhs') | (lhs', rhs') <- zip lhs_tl rhs_tl ] scope_env
            else fail "unifying-failed: case=RigidRigid, cause=head-not-matched-or-args-length-not-matched"
        | (LVar x, params) <- viewNApps lhs
        = if (x, params) `isPatternWrt` scope_env
            then mksubst x params rhs
            else giveup NotAPattern
        | (LVar x, params) <- viewNApps rhs
        = if (x, params) `isPatternWrt` scope_env
            then mksubst x params lhs
            else giveup NotAPattern
        | otherwise
        = giveup SpecialPrim
        where
            mksubst :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> StateT HasSolvedAtLeastOneProblem (MaybeT m) ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
            mksubst x params rhs = do
                res <- lift $ runExceptT (callSimpleMkRef x params rhs scope_env)
                case res of
                    Left bad_res -> giveup bad_res
                    Right good_res -> do
                        put True
                        return ([], good_res)
            giveup :: Monad m => MkRefFailed -> m ([Disagreement], (Labeling, [(LogicVar, TermNode)]))
            giveup _ = return ([foldNLams (lambda, lhs) :=?=: foldNLams (lambda, rhs)], (scope_env, []))

callSimpleMkRef :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> Labeling -> ExceptT MkRefFailed (MaybeT m) (Labeling, [(LogicVar, TermNode)])
callSimpleMkRef = entryOfSimpleMkRef where
    entryOfSimpleMkRef :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> TermNode -> Labeling -> ExceptT MkRefFailed (MaybeT m) (Labeling, [(LogicVar, TermNode)])
    entryOfSimpleMkRef x params rhs scope_env
        | (l', rhs') <- viewNLams rhs
        , (LVar x', rhs_args) <- viewNApps rhs'
        , x == x'
        = do
            let n = length rhs_args
                lhs_args = map (liftLams l') params ++ map mkNIdx [l' - 1, l' - 2 .. 0]
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
            (refined_rhs, (new_scope_env, lvar_bindings)) <- bindsLVarToRefinedEvalRef x params 0 rhs (scope_env, [])
            return (new_scope_env, (x, foldNLams (l, refined_rhs)) : lvar_bindings) -- FIXED: refined_rhs --> foldNLams (l, refined_rhs)
        where
            l :: SmallNat
            l = length params
    bindsLVarToRefinedEvalRef :: GeneratingUniqueMonad m => LogicVar -> [TermNode] -> SmallNat -> TermNode -> (Labeling, [(LogicVar, TermNode)]) -> ExceptT MkRefFailed (MaybeT m) (TermNode, (Labeling, [(LogicVar, TermNode)]))
    bindsLVarToRefinedEvalRef x params l rhs (scope_env, lvar_bindings_acc)
        | (l', rhs') <- viewNLams rhs
        , l' > 0
        = do
            (refined_rhs', (scope_env', (lvar_bindings_acc'))) <- bindsLVarToRefinedEvalRef x params (l + l') rhs' (scope_env, lvar_bindings_acc)
            return (foldNLams (l', refined_rhs'), (scope_env', lvar_bindings_acc'))
        | (rhs_hd, rhs_tl) <- viewNApps rhs
        , isRigid rhs_hd
        = do
            refined_rhs_hd <- case rhs_hd of
                NIdx i -> case down1 rhs_hd (map (liftLams l) params ++ map mkNIdx [l - 1, l - 2 .. 0]) of
                    Just r -> return r
                    _ -> fail "unifying-failed: case=FlexRigid, cause=imitation-failed"
                r -> if dukeOfCon scope_env (\r_scope -> viewScope x scope_env >= r_scope) r
                    then return r
                    else fail "unifying-failed: case=FlexRigid, cause=imitation-failed"
            (refined_rhs_tl, (scope_env', lvar_bindings_acc')) <- runStateT (mapM (StateT . bindsLVarToRefinedEvalRef x params l) rhs_tl) (scope_env, lvar_bindings_acc)
            return (foldNApps (refined_rhs_hd, refined_rhs_tl), (scope_env', lvar_bindings_acc'))
        | (LVar y, rhs_args) <- viewNApps rhs
        = if x == y
            then fail "unifying-failed: case=FlexFlex, cause=occurs-check-failed"
            else do
                let lhs_args = map (liftLams l) params ++ map mkNIdx [l - 1, l - 2 .. 0]
                    com_args = Set.toList (Set.fromList lhs_args `Set.intersection` Set.fromList rhs_args)
                    x_scope = viewScope x scope_env
                    y_scope = viewScope y scope_env
                    x_outer = com_args `down` lhs_args
                    y_outer = com_args `down` rhs_args
                if (y, rhs_args) `isPatternWrt` scope_env
                    then do
                        h <- getNewUnique
                        let myResult x_inner y_inner = (foldNApps (mkLVar h, x_inner ++ x_outer), (Map.insert h (min x_scope y_scope) scope_env, (y, foldNLams (length rhs_args, foldNApps (mkLVar h, y_inner ++ y_outer))) : lvar_bindings_acc))
                        if x_scope < y_scope
                            then do
                                y_inner <- runReaderT (lhs_args `up` y) scope_env
                                let x_inner = y_inner `down` lhs_args
                                return (myResult x_inner y_inner)
                            else do
                                x_inner <- runReaderT (rhs_args `up` x) scope_env
                                let y_inner = x_inner `down` rhs_args
                                return (myResult x_inner y_inner)
                    else throwE NotAPattern
        | otherwise
        = throwE SpecialPrim
    down1 :: TermNode -> [TermNode] -> Maybe TermNode
    down1 param args = fmap (\i -> mkNIdx (length args - 1 - i)) (param `List.elemIndex` args)
    down :: [TermNode] -> [TermNode] -> [TermNode]
    params `down` args = map (fromJust . flip down1 args) params
    up :: Monad m => [TermNode] -> LogicVar -> ReaderT Labeling m [TermNode]
    cs `up` x = ask >>= \scope_env -> return (filter (dukeOfCon scope_env (\c_scope -> viewScope x scope_env >= c_scope)) cs)

{- Comments on Basic Idea -}

{- Contents 
1. Term simplication in higher-order pattern unification [no impl]
2. Top-level control for calculating variable bindings   [impl in \S4]
3. Calculating variable bindings                         [impl in \S5]
-}

{- Section 1 -}

{- Notations
01. {| t, ol, nl, env |} stands for (rewriteWithSusp t ol nl env NF).
>   t is the evaluatee.
>   ol is the length of env.
>   nl counts how many binders we have encountered.
>   env is the de-bruijn indices context of variables, which are bound by binders we have encountered.
>   DbIdxCtx ::= [] | Dummy l :: DbIdxCtx | Binds t l :: DbIdxCtx
>   Dummy l refers the variable bound by the l-th binder, which has no evaluation reference.
>   Binds t l refers the variable bound by the l-th binder, whose evaluation reference is t.
02. An atomic term is either a flex var, a rigid var or a de-bruijn index.
03. app(t, ts) denotes the term (foldNApps t ts); where t is an atom, and ts is a list of NFs.
04. lam(l). t denotes the term (foldNLams l t); where t is a NF but not a lambda-abstraction.
05. eta(l, app(t, [z_1 .. z_n])) = lam(l). app({| t, 0, l, [] |}, [{| z_1, 0, l, [] |} .. {| z_n, 0, l, [] |}] ++ [#(l - 1) .. #0]).
06. An atomic term x is called the head of t if t = lam(l). app(x, zs) for some l and zs.
07. [w_1 .. w_m] is a position of [z_1 .. z_m] in [t_1 .. t_n] if,
>   for any k in [1 .. m], there exists i in [1 .. n] such that w_k = #(n - i) and t_i = z_k.
#                                                                     ^^^^^^^^ In [1], it is written to be #(n + i).
-}

{- Section 2 -}

{- ${Term} is a L_lambda-pattern in ${Env}.
(1) RULE[ higher-order pattern ]
> X is a flex var.
> env.evalref X == none.
> Every element of zs is a de-bruijn index or a rigid var.
> For any rigid var c in zs, env.scopelv X < env.scopelv c.
===========================================================
> app(X, zs) is a L_lambda-pattern in env.
-}

{- Section 3 -}

{- ${Env} = ${Env} |> ${Var} :==> ${Term}.
(1) RULE[ reflect non-trivial subst ]
> X is a flex var.
> env.evalref X == None.
> X is not a member of FreeLVs(t).
> For any flex var Y: env'.evalref Y = Some t,         if X ==_{alpha} Y;
>                                    = Some s[X := t], else if Some s = env.evalref Y;
>                                    = None,           else.
> For any flex var Y: env'.scopelv Y = min {env.scopelv X, env.scopelv Y}, if Y is a member of FreeLVs(t);
>                                    = env.scopelv Y,                      else.
==========================================================================================================
> env' = env |> X :==> t.
(2) RULE[ reflect trivial subst ]
> X is a flex var.
========================
> env = env |> X :==> X.
-}

{- Section 4 -}

-- Top-level control for calculating variable bindings

{- ${Env} ~~> MkRef[ ${Term} := ${Term} ] ~~> ${Env} with { newQs = ${Constraints} }.
(1) RULE[ FlexFlex(same heads) ]
> app(X, [a_1 .. a_n]) is a L_lambda-pattern in env.
> app(X, [b_1 .. b_(n + l)]) is a L_lambda-pattern in env.
> env.evalref X == None.
> as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
> zs = [ #(n + l - i) | i <- [1 .. n + l], as !! (i - 1) == b_i ].
> env' = env |> new flex var H = { evalref = None, scopelv = env.scopelv X }.
> env'' = env' |> X :==> lam(n + l). app(H, zs).
============================================================================================================
> env ~~> MkRef[ app(X, [a_1 .. a_n]) := lam(l). app(X, [b_1 .. b_(n + l)]) ] ~~> env'' with { newQs = [] }.
(2) RULE[ binding ]
> app(X, [a_1 .. a_n]) is a L_lambda-pattern in env.
> The head of t is not X.
> env.evalref X == None.
> env ~~> Bind_{0}[ app(X, [a_1 .. a_n]) +-> t ] = s ~~> env', if probs hold.
> env'' = env' |> X :==> lam(n). s.
==============================================================================
> env ~~> MkRef[ app(X, [a_1 .. a_n]) := t ] ~~> env'' with { newQs = probs }.
-}

{- Section 5 -}

-- Calculating variable bindings

{- ${Env} ~~> Bind_{${Nat}}[ ${Term} +-> ${Term} ] = ${Term} ~~> ${Env}, if ${Constraints} hold.
(1) RULE[ BindLam ]
> env ~~> Bind_{l + m}[ app(X, [a_1 .. a_n]) +-> t ] = s ~~> env', if probs hold.
> m is a positive integer.
=============================================================================================
> env ~~> Bind_{l}[ app(X, [a_1 .. a_n]) +-> lam(m). t ] = lam(m). s ~~> env', if probs hold.
(2) RULE[ FlexRigid ]
> r is a rigid var or a de-bruijn index.
> as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
> r' = r,  if r is a rigid var such that env.scopelv X >= env.scopelv r;
>    = #i, if r is a de-bruijn index with r ==_{alpha} as !! i.
> For k in [1 .. m]: env_{k - 1} ~~> Bind_{l}[ app(X, [a_1 .. a_n]) +-> t_k ] = s_k ~~> env_{k}, if probs_k hold.
=================================================================================================================================================
> env_{0} ~~> Bind_{l}[ app(X, [a_1 .. a_n]) +-> app(r, [t_1 .. t_m]) ] = app(r', [s_1 .. s_m]) ~~> env_{m}, if concat [probs_1 .. probs_m] hold.
(3) RULE[ FlexFlex(different heads, rhs head invisible) ]
> X and Y are different flex vars.
> app(Y, [b_1 .. b_m]) is a L_lambda-pattern in env.
> env.scopelv X < env.scopelv Y.
> as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
> cs is the sublist of as whose elements are rigid vars and visible to Y.
> ws is a position of cs in as.
> zs is a permutation of { as !! (i - 1) | i <- {1 .. n + l} } `intersection` {b_1 .. b_m}.
> us is a position of zs in [b_1 .. b_m].
> vs is a position of zs in as.
> env' = env |> new flex var H = { evalref = None, scopelv = env.scopelv X }.
> env'' = env' |> Y :==> app(H, cs ++ us).
=============================================================================================================
> env ~~> Bind_{l}[ app(X, [a_1 .. a_n]) +-> app(Y, [b_1 .. b_m]) ] = app(H, ws ++ vs) ~~> env'', if [] hold.
(4) RULE[ FlexFlex(different heads, rhs head visible) ]
> X and Y are different flex vars.
> app(Y, [b_1 .. b_m]) is a L_lambda-pattern in env.
> env.scopelv X >= env.scopelv Y.
> as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
> cs is the sublist of [b_1 .. b_m] whose elements are rigid vars and visible to X.
> ws is a position of cs in [b_1 .. b_m].
> zs is a permutation of { as !! (i - 1) | i <- {1 .. n + l} } `intersection` {b_1 .. b_m}.
> us is a position of zs in as.
> vs is a position of zs in [b_1 .. b_m].
> env' = env |> new flex var H = { evalref = None, scopelv = env.scopelv Y }.
#                                                            ^^^^^^^^^^^^^ In [1], it is written to be env.scopelv X.
> env'' = env' |> Y :==> app(H, ws ++ vs).
=====================================================================================================================
> env ~~> Bind_{l}[ app(X, [a_1 .. a_n]) +-> app(Y, [b_1 .. b_m]) ] = app(H, cs ++ us) ~~> env'', if [] hold.
-}

{- References
[1] @article{DBLP:journals/corr/abs-0911-5203
    , author     = {Xiaochu Qi}
    , title      = {An Implementation of the Language Lambda Prolog Organized around Higher-Order Pattern Unification}
    , journal    = {CoRR}
    , volume     = {abs/0911.5203}
    , year       = {2009}
    , url        = {http://arxiv.org/abs/0911.5203}
    , eprinttype = {arXiv}
    , eprint     = {0911.5203},
    , timestamp  = {Mon, 13 Aug 2018 16:48:41 +0200}
    , biburl     = {https://dblp.org/rec/journals/corr/abs-0911-5203.bib}
    , bibsource  = {dblp computer science bibliography, https://dblp.org}
    }
-}
