module Jasmine.Alpha1.Header.TermNode.DeBruijn where

import Data.List (elemIndex)
import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.Util
import Z.Algo.Function

rewriteWithSusp :: TermNode -> Nat_ol -> Nat_nl -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSusp (NIdx i) ol nl env option
    | i >= ol = mkNIdx (i - ol + nl)
    | i >= 0 = case env !! i of
        Dummy l -> mkNIdx (nl - l)
        Binds t l -> rewriteWithSusp t 0 (nl - l) [] option
    | otherwise = error "A negative de-bruijn index."
rewriteWithSusp (NApp t1 t2) ol nl env option
    | option == ALPHA = mkNApp (rewriteWithSusp t1 ol nl env option) (rewriteWithSusp t2 ol nl env option)
    | otherwise = case rewriteWithSusp t1 ol nl env WHNF of
        NLam t -> case t of
            Susp t' ol' nl' (Dummy l : env')
                | nl' == l -> rewriteWithSusp t' ol' (pred nl') (mkBinds (mkSusp t2 ol nl env) (pred l) : env') option
            t -> rewriteWithSusp t 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
        t1' -> case option of
            NF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
            HNF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (mkSusp t2 ol nl env)
            WHNF -> mkNApp t1' (mkSusp t2 ol nl env)
rewriteWithSusp (NLam t1) ol nl env option
    | option == WHNF = mkNLam (mkSusp t1 (succ ol) (succ nl) (mkDummy (succ nl) : env))
    | otherwise = mkNLam (rewriteWithSusp t1 (succ ol) (succ nl) (mkDummy (succ nl) : env) option)
rewriteWithSusp (Susp t ol nl env) ol' nl' env' option
    | ol == 0 && nl == 0 = rewriteWithSusp t ol' nl' env' option
    | ol' == 0 = rewriteWithSusp t ol (nl + nl') env option
    | otherwise = case rewriteWithSusp t ol nl env WHNF of
        NLam t1
            | option == WHNF -> mkNLam (mkSusp t1 (succ ol') (succ nl') (mkDummy (succ nl') : env'))
            | otherwise -> mkNLam (rewriteWithSusp t1 (succ ol') (succ nl') (mkDummy (succ nl') : env') option)
        t' -> rewriteWithSusp t' ol' nl' env' option
rewriteWithSusp t ol nl env option
    = t

rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = rewriteWithSusp t 0 0 [] option

toDeBruijn :: LambdaTerm (Either LogicVar Constructor) -> TermNode
toDeBruijn = go [] where
    go :: [MyIVar] -> LambdaTerm (Either LogicVar Constructor) -> TermNode
    go ys (Var x) = mkNIdx (fromJust (x `elemIndex` ys))
    go ys (Con c) = either mkLVar mkNCon c
    go ys (App t1 t2) = mkNApp (go ys t1) (go ys t2)
    go ys (Lam y t1) = mkNLam (go (y : ys) t1)
