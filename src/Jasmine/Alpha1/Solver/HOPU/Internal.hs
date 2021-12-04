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
(5) For t = lam(l). app(x, zs), the head of t is x if x is a var.
-}

{- ${Term} is a L_lambda-pattern in ${Env}
(1) RULE[ higher-order pattern ]
    X is a flex var.
    env.evalref X == none.
    Every element of zs is a de-bruijn index or a rigid var.
    For any rigid var c in zs, env.socpe X < env.scope c.
    ========================================================
    app(X, zs) is a L_lambda-pattern in env.
-}

{- ${LVar} +-> ${Term} yields ${Env} ~~> ${Env}
(1) RULE[ update env by subst ]
    X is a flex var.
    env.evalref X == none.
    X is not a member of FreeLVs(t).
    env'.evalref v
        = some t,        if v ==_{alpha} X;
        = env.evalref v, otherwise.
    env'.scope v
        = min (env.scope X) (env.scope v), if v is a member of FreeLVs(t);
        = env.scope v,                     otherwise.
    ======================================================================
    X +-> t yields env ~~> env'.
-}

{- ${Env} ~~> MkRef[ ${Term} := ${Term} ] ~~> ${Env} with { newQs = ${Constraints} }
(1) RULE[ flex-flex common head ]
    app(X, [a_1 .. a_n]) is a L_lambda-pattern in env.
    app(X, [b_1 .. b_(n + l)]) is a L_lambda-pattern in env.
    env.evalref X == none.
    as = [{| a_1, 0, l, [] |} .. {| a_n, 0, l, [] |}] ++ [#(l - 1) .. #0].
    zs = [ #(n + l - i) | i <- [1 .. n + l], as !! (i - 1) == b_i ].
    env' = env
        |> new flex var H = { evalref = none, scope = env.scope X }
        let t = lam(n + l). app(H, zs) in
        |> update this.evalref X = (if t ==_{beta} eta(l, X) then none else some t).
    =========================================================================================================
    env ~~> MkRef[ app(X, [a_1 .. a_n]) := lam(l). app(X, [b_1 .. b_(n + l)]) ] ~~> env' with { newQs = [] }.
(2) RULE[ binding ]
    app(X, [a_1 .. a_n]) is a L_lambda-pattern in env
    The head of rhs is not X.
    env.evalref X == none.
    env |= Bind[ app(X, [a_1 .. a_n]) +-> rhs ] = t if probs satisfied.
    X +-> t yields env ~~> env'
    =============================================================================
    env ~~> MkRef[ app(X, [a_1 .. a_n]) := rhs ] ~~> env' with { newQs = probs }.
-}

{- ${Env} |= Bind[ ${Term} +-> ${Term} ] = {$Term} if ${Constraints} satisfied.

-}
