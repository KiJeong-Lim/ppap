module Jasmine.Alpha1.Solver.HOPU.Internal where

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
import Jasmine.Alpha1.Solver.HOPU.Util
import Z.Algo.Function
import Z.Utils

{- Notations
(1) {| t, ol, nl, env |} stands for rewriteWithSusp t ol nl env NF.
    t is the evaluatee.
    ol is the length of $env$.
    nl counts how many binders we have encountered.
    env is the de-bruijn indices context of variables, which are bound by binders we have encountered.
    DbIdxCtx ::= [] | Dummy l :: DbIdxCtx | Binds t l :: DbIdxCtx
    Dummy l refers the variable bound by the l-th binder, which has no evaluation reference.
    Binds t l refers the variable bound by the l-th binder, whose evaluation reference is t.
(2) app(t, ts) stands for foldNApps t ts.
(3) lam(l). t stands for foldNLams l t.
(4) eta(l, app(t, [z_1 .. z_n]))
    = lam(l). app({| t, 0, l, [] |}, [{| z_1, 0, l, [] |} .. {| z_n, 0, l, [] |}] ++ [#(l - 1) .. #0]).
(5) For t = lam(l). app(x, zs),
    the head of t is x if x is a var.
-}

{- ${Term} is a L_lambda-pattern in ${Env}
(1) RULE[ higher-order pattern ]
    > X is a flex var.
    > env.evalref X == none.
    > Every element of zs is a de-bruijn index or a rigid var.
    > For any rigid var c in zs, env.socpe X < env.scope c.
    ==========================================================
    > app(X, zs) is a L_lambda-pattern in env.
-}

{- ${LVar} +-> ${Term} yields ${Env} ~~> ${Env}
(1) RULE[ update env by subst ]
    > X is a flex var.
    > env.evalref X == none.
    > X is not a member of FreeLVs(t).
    > env'.evalref v
    >   = some t,        if v ==_{alpha} X;
    >   = env.evalref v, otherwise.
    > env'.scope v
    >   = min (env.scope X) (env.scope v), if v is a member of FreeLVs(t);
    >   = env.scope v,                     otherwise.
    ======================================================================
    > X +-> t yields env ~~> env'.
-}

{- ${Env} ~~> MkRef[ ${Term} := ${Term} ] ~~> ${Env} with { newQs = ${Constraints} }
(1) RULE[ flex-flex common head case ]
    > app(X, [a_1 .. a_n]) is a L_lambda-pattern in env.
    > app(X, [b_1 .. b_(n + l)]) is a L_lambda-pattern in env.
    > env.evalref X == none.
    > as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
    > zs = [ #(n + l - i) | i <- [1 .. n + l], as !! (i - 1) == b_i ].
    > env' = env
    >   |> new flex var H = { evalref = none, scope = env.scope X }
    >   let t = lam(n + l). app(H, zs) in
    >   |> update this.evalref X = (if t ==_{beta} eta(l, X) then none else some t).
    ===========================================================================================================
    > env ~~> MkRef[ app(X, [a_1 .. a_n]) := lam(l). app(X, [b_1 .. b_(n + l)]) ] ~~> env' with { newQs = [] }.
(2) RULE[ binding ]
    > app(X, [a_1 .. a_n]) is a L_lambda-pattern in env
    > The head of t is not X.
    > env.evalref X == none.
    > env |= Bind_{0}[ app(X, [a_1 .. a_n]) +-> t ] = s, if probs satisfied.
    > X +-> lam(n). s yields env ~~> env'.
    =============================================================================
    > env ~~> MkRef[ app(X, [a_1 .. a_n]) := t ] ~~> env' with { newQs = probs }.
-}

{- ${Env} |= Bind_{${Nat}}[ ${Term} +-> ${Term} ] = ${Term}, if ${Constraints} satisfied.
(1) RULE[ BindLam ]
    > env |= Bind_{l + m}[ app(X, [a_1 .. a_n]) +-> t ] = s if probs satisfied.
    > m is a positive integer.
    =======================================================================================
    > env |= Bind_{l}[ app(X, [a_1 .. a_n]) +-> lam(m). t ] = lam(m). s if probs satisfied.
(2) RULE[ FlexRigid ]
    > as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
    > r' = r,  if r is a rigid var such that env.scope X >= env.scope r;
    >    = #i, if r is a de-bruijn index with r ==_{alpha} as !! i.
    > For k in [1 .. m],
    > env |= Bind_{l}[ app(X, [a_1 .. a_n]) +-> t_k ] = s_k if probs_k satisfied.
    ====================================================================================================================================
    > env |= Bind_{l}[ app(X, [a_1 .. a_n]) +-> app(r, [t_1 .. t_m]) ] = app(r', [s_1 .. s_m]) if concat [probs_1 .. probs_m] satisfied.
-}
