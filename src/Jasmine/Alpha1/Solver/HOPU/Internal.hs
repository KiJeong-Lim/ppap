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

{- Comments on Basic Idea -}

{- Contents 
1. Term simplication in higher-order pattern unification [no impl]
2. Top-level control for calculating variable bindings   [impl in \S3]
3. Calculating variable bindings                         [impl in \S4]
-}

{- Section 0 -}

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

{- Section 1 -}

{- ${Term} is a L_lambda-pattern in ${Env}.
(1) RULE[ higher-order pattern ]
> X is a flex var.
> env.evalref X == none.
> Every element of zs is a de-bruijn index or a rigid var.
> For any rigid var c in zs, env.scopelv X < env.scopelv c.
===========================================================
> app(X, zs) is a L_lambda-pattern in env.
-}

{- Section 2 -}

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

{- Section 3 -}

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

{- Section 4 -}

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
