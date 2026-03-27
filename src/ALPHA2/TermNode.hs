module ALPHA2.TermNode where

import ALPHA2.Constant
import ALPHA2.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type DeBruijn = Int

type SuspEnv = [SuspItem]

type IsTypeLevel = Bool

data LogicVar
    = LV_ty_var Unique
    | LV_Unique Unique
    | LV_Named LargeId
    deriving (Eq, Ord)

data TermNode
    = LVar LogicVar
    | NCon Constant
    | NIdx DeBruijn
    | NApp TermNode TermNode
    | NLam TermNode
    | Susp
        { getSuspBody :: TermNode
        , getSuspOL :: Int
        , getSuspNL :: Int
        , getSuspEnv :: SuspEnv
        }
    deriving (Eq, Ord)

data SuspItem
    = Dummy Int
    | Binds TermNode Int
    deriving (Eq, Ord)

data ReduceOption
    = WHNF
    | HNF
    | NF
    deriving (Eq)

data Fixity extra
    = Prefix String extra
    | InfixL extra String extra
    | InfixR extra String extra
    | InfixN extra String extra
    deriving ()

data ViewNode
    = ViewIVar Int
    | ViewLVar LargeId
    | ViewDCon SmallId
    | ViewIApp ViewNode ViewNode
    | ViewIAbs Int ViewNode
    | ViewTVar LargeId
    | ViewTCon SmallId
    | ViewTApp ViewNode ViewNode
    | ViewOper (Fixity ViewNode, Precedence)
    | ViewNatL Integer
    | ViewChrL Char
    | ViewStrL String
    | ViewList [ViewNode]
    deriving ()

instance Show TermNode where
    showsPrec prec = pprint prec . constructViewer

instance Outputable ViewNode where
    pprint prec = go where
        parenthesize :: Precedence -> (String -> String) -> String -> String
        parenthesize prec' delta
            | prec > prec' = strstr "(" . delta . strstr ")"
            | otherwise = delta
        go :: ViewNode -> String -> String
        go (ViewIVar var) = strstr "W_" . showsPrec 0 var
        go (ViewLVar var) = strstr var
        go (ViewDCon con) = strstr con
        go (ViewIApp viewer1 viewer2) = parenthesize 6 (pprint 6 viewer1 . strstr " " . pprint 7 viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr "W_" . showsPrec 0 var . strstr "\\ " . pprint 0 viewer1)
        go (ViewTVar var) = strstr var
        go (ViewTCon con) = strstr con
        go (ViewTApp viewer1 viewer2) = parenthesize 6 (pprint 6 viewer1 . strstr " " . pprint 7 viewer2)
        go (ViewOper (oper, prec')) = case oper of
            Prefix str viewer1 -> parenthesize prec' (strstr str . pprint prec' viewer1)
            InfixL viewer1 str viewer2 -> parenthesize prec' (pprint prec' viewer1 . strstr str . pprint (prec' + 1) viewer2)
            InfixR viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint prec' viewer2)
            InfixN viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint (prec' + 1) viewer2)
        go (ViewChrL chr) = showsPrec 0 chr
        go (ViewStrL str) = showsPrec 0 str
        go (ViewNatL nat) = showsPrec 0 nat
        go (ViewList viewers) = strstr "[" . ppunc ", " (map (pprint 5) viewers) . strstr "]"

instance Show LogicVar where
    showsPrec prec (LV_ty_var uni) = strstr "?TV_" . showsPrec prec (unUnique uni)
    showsPrec prec (LV_Unique uni) = strstr "?LV_" . showsPrec prec (unUnique uni)
    showsPrec prec (LV_Named name) = strstr name

mkLVar :: LogicVar -> TermNode
mkLVar v = v `seq` LVar v

mkNCon :: ToConstant a => a -> TermNode
mkNCon = go . makeConstant where
    go :: Constant -> TermNode
    go c = c `seq` NCon c

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = i `seq` NIdx i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (NCon (DC (DC_Succ))) (NCon (DC (DC_NatL n))) = let n' = n + 1  in n' `seq` mkNCon (DC_NatL n')
mkNApp t1 t2 = t1 `seq` t2 `seq` NApp t1 t2

mkNLam :: TermNode -> TermNode
mkNLam t = t `seq` NLam t

mkSusp :: TermNode -> Int -> Int -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl env = t `seq` ol `seq` nl `seq` env `seq` Susp { getSuspBody = t, getSuspOL = ol, getSuspNL = nl, getSuspEnv = env }

mkDummy :: Int -> SuspItem
mkDummy l = l `seq` Dummy l

mkBinds :: TermNode -> Int -> SuspItem
mkBinds t l = t `seq` l `seq` Binds t l

rewriteWithSusp :: TermNode -> Int -> Int -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSusp t ol nl env option = dispatch t where
    dispatch :: TermNode -> TermNode
    dispatch (LVar {})
        = t
    dispatch (NIdx i)
        | i >= ol = mkNIdx (i - ol + nl)
        | i >= 0 = case env !! i of
            Dummy l -> mkNIdx (nl - l)
            Binds t' l -> rewriteWithSusp t' 0 (nl - l) [] option
        | otherwise = error "***normalizeWithSuspEnv: A negative De-Bruijn index given..."
    dispatch (NCon {})
        = t
    dispatch (NApp t1 t2)
        | NLam t11 <- t1' = beta t11
        | option == WHNF = mkNApp t1' (Susp t2 ol nl env)
        | option == HNF = mkNApp (rewriteWithSusp t1' 0 0 [] option) (Susp t2 ol nl env)
        | option == NF = mkNApp (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
        where
            t1' :: TermNode
            t1' = rewriteWithSusp t1 ol nl env WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' ol' nl' (Dummy l' : env'))
                | nl' == l' = rewriteWithSusp t' ol' (pred nl') (mkBinds (mkSusp t2 ol nl env) (pred l') : env') option
            beta t' = rewriteWithSusp t' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
    dispatch (NLam t1)
        | option == WHNF = mkNLam (Susp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
        | otherwise = mkNLam (rewriteWithSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option)
    dispatch (Susp t' ol' nl' env')
        | ol' == 0 && nl' == 0 = rewriteWithSusp t' ol nl env option
        | ol == 0 = rewriteWithSusp t' ol' (nl + nl') env' option
        | otherwise = rewriteWithSusp (rewriteWithSusp t' ol' nl' env' WHNF) ol nl env option

rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = rewriteWithSusp t 0 0 [] option

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NCon (DC (DC_NatL n))) ts
        | n == 0 = (mkNCon (DC_NatL 0), ts)
        | n > 0 = let n' = n - 1 in n' `seq` (mkNCon DC_Succ, mkNCon (DC_NatL n') : ts)
        | otherwise = error "`unfoldlNApp\': negative integer"
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

lensForSuspEnv :: (TermNode -> TermNode) -> SuspEnv -> SuspEnv
lensForSuspEnv delta = map go where
    go :: SuspItem -> SuspItem
    go (Dummy l) = mkDummy l
    go (Binds t l) = mkBinds (delta t) l

foldlNApp :: TermNode -> [TermNode] -> TermNode
foldlNApp = List.foldl' mkNApp

makeNestedNLam :: Int -> TermNode -> TermNode
makeNestedNLam n
    | n == 0 = id
    | n > 0 = makeNestedNLam (n - 1) . mkNLam
    | otherwise = undefined

viewNestedNLam :: TermNode -> (Int, TermNode)
viewNestedNLam = go 0 where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NLam t) = go (n + 1) t
    go n t = (n, t)

constructViewer :: TermNode -> ViewNode
constructViewer = fst . runIdentity . uncurry (runStateT . formatView . eraseType) . runIdentity . flip runStateT 1 . makeView [] . rewrite NF where
    isType :: ViewNode -> Bool
    isType (ViewTVar _) = True
    isType (ViewTCon _) = True
    isType (ViewTApp _ _) = True
    isType _ = False
    makeView :: [Int] -> TermNode -> StateT Int Identity ViewNode
    makeView vars (LVar var) = case var of
        LV_ty_var v -> return (ViewTVar ("?TV_" ++ show v))
        LV_Unique v -> return (ViewLVar ("?V_" ++ show v))
        LV_Named v -> return (ViewLVar v)
    makeView vars (NCon con) = case con of
        DC data_constructor -> case data_constructor of
            DC_LO logical_operator -> return (ViewDCon (show logical_operator))
            DC_Named name -> return (ViewDCon ("__" ++ name))
            DC_Unique uni -> return (ViewDCon ("c_" ++ show uni))
            DC_Nil -> return (ViewDCon "[]")
            DC_Cons -> return (ViewDCon "::")
            DC_ChrL chr -> return (ViewChrL chr)
            DC_NatL nat -> return (ViewNatL nat)
            DC_Succ -> return (ViewDCon "__s")
            DC_eq -> return (ViewDCon "=")
            DC_le -> return (ViewDCon "=<")
            DC_lt -> return (ViewDCon "<")
            DC_ge -> return (ViewDCon ">=")
            DC_gt -> return (ViewDCon ">")
            DC_plus -> return (ViewDCon "+")
            DC_minus -> return (ViewDCon "-")
            DC_mul -> return (ViewDCon "*")
            DC_div -> return (ViewDCon "/")
            DC_wc -> return (ViewDCon "_")
        TC type_constructor -> case type_constructor of
            TC_Arrow -> return (ViewTCon "->")
            TC_Unique uni -> return (ViewTCon ("tc_" ++ show uni))
            TC_Named name -> return (ViewTCon ("__" ++ name))
    makeView vars (NIdx idx) = return (ViewIVar (vars !! idx))
    makeView vars (NApp t1 t2) = do
        t1_rep <- makeView vars t1
        t2_rep <- makeView vars t2
        return (if isType t1_rep then ViewTApp t1_rep t2_rep else ViewIApp t1_rep t2_rep)
    makeView vars (NLam t) = do
        var <- get
        let var' = var + 1
        put var'
        t_rep <- makeView (var : vars) t
        return (ViewIAbs var t_rep)
    eraseType :: ViewNode -> ViewNode
    eraseType (ViewIApp (ViewDCon "[]") (ViewTCon "__char")) = ViewStrL ""
    eraseType (ViewTCon c) = ViewTCon c
    eraseType (ViewTApp t1 t2) = ViewTApp (eraseType t1) (eraseType t2)
    eraseType (ViewIVar v) = ViewIVar v
    eraseType (ViewLVar v) = ViewLVar v
    eraseType (ViewTVar v) = ViewTVar v
    eraseType (ViewIAbs v t) = ViewIAbs v (eraseType t)
    eraseType (ViewIApp t1 t2) = if isType t2 then eraseType t1 else ViewIApp (eraseType t1) (eraseType t2)
    eraseType (ViewNatL nat) = ViewNatL nat
    eraseType (ViewChrL chr) = ViewChrL chr
    eraseType (ViewDCon c) = ViewDCon c
    checkOper :: String -> Maybe (Fixity (), Precedence)
    checkOper "->" = Just (InfixR () " -> " (), 4)
    checkOper "::" = Just (InfixR () " :: " (), 4)
    checkOper "Lambda" = Just (Prefix "Lambda " (), 0)
    checkOper ":-" = Just (InfixR () " :- " (), 0)
    checkOper ";" = Just (InfixL () "; " (), 1)
    checkOper "," = Just (InfixL () ", " (), 3)
    checkOper "=>" = Just (InfixR () " => " (), 2)
    checkOper "pi" = Just (Prefix "pi " (), 5)
    checkOper "sigma" = Just (Prefix "sigma " (), 5)
    checkOper "=" = Just (InfixN () " = " (), 5)
    checkOper "=<" = Just (InfixN () " =< " (), 5)
    checkOper "<" = Just (InfixN () " < " (), 5)
    checkOper ">=" = Just (InfixN () " >= " (), 5)
    checkOper ">" = Just (InfixN () " > " (), 5)
    checkOper "is" = Just (InfixN () " is " (), 5)
    checkOper "+" = Just (InfixN () " + " (), 6)
    checkOper "-" = Just (InfixN () " - " (), 6)
    checkOper "*" = Just (InfixN () " * " (), 7)
    checkOper "/" = Just (InfixN () " / " (), 7)
    checkOper _ = Nothing
    formatView :: ViewNode -> StateT Int Identity ViewNode
    formatView (ViewDCon "[]") = return (ViewList [])
    formatView (ViewIApp (ViewIApp (ViewDCon "::") (ViewChrL chr)) t) = do
        t' <- formatView t
        case t' of
            ViewStrL str -> return (ViewStrL (chr : str))
            t' -> return (ViewOper (InfixR (ViewChrL chr) " :: " t', 4))
    formatView (ViewIApp (ViewIApp (ViewDCon "::") t1) t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        case t2' of
            ViewList ts -> return (ViewList (t1' : ts))
            _ -> return (ViewOper (InfixR t1' " :: " t2', 4))
    formatView (ViewIApp (ViewIApp (ViewDCon con) t1) t2)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewIApp (ViewOper (Prefix str t1', prec)) t2')
            InfixL _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixL t1' str t2', prec))
            InfixR _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixR t1' str t2', prec))
            InfixN _ str _ -> do
                t1' <- formatView t1
                t2' <- formatView t2
                return (ViewOper (InfixN t1' str t2', prec))
    formatView (ViewIApp (ViewDCon con) t1)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView t1
                return (ViewOper (Prefix str t1', prec))
            InfixL _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixL t1' str (ViewIVar v2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixR t1' str (ViewIVar v2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                return (ViewIAbs v2 (ViewOper (InfixN t1' str (ViewIVar v2), prec)))
    formatView (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                v1 <- get
                put (v1 + 1)
                return (ViewIAbs v1 (ViewOper (Prefix str (ViewIVar v1), prec)))
            InfixL _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixL (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixR _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixR (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixN _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                return (ViewIAbs v1 (ViewIAbs v2 (ViewIAbs v2 (ViewOper (InfixN (ViewIVar v1) str (ViewIVar v2), prec)))))
    formatView (ViewTApp (ViewTApp (ViewTCon "->") t1) t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewOper (InfixR t1' " -> " t2', 4))
    formatView (ViewIApp t1 t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewIApp t1' t2')
    formatView (ViewTApp t1 t2) = do
        t1' <- formatView t1
        t2' <- formatView t2
        return (ViewTApp t1' t2')
    formatView (ViewIAbs v1 t2) = do
        t2' <- formatView t2
        return (ViewIAbs v1 t2')
    formatView (ViewDCon ('_' : '_' : c)) = return (ViewDCon c)
    formatView (ViewTCon ('_' : '_' : c)) = return (ViewTCon c)
    formatView viewer = return viewer
