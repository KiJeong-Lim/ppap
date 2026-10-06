module Hol.ALPHA1.Back.Base.TermNode.Show where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Front.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Utils hiding (Outputable, pprint, pshow, Indentation, ErrMsg, Unique, unUnique, UniqueT, runUniqueT, HasAnnot, getAnnot, setAnnot, strstr, strcat, nl, pindent, ppunc, plist', plist, quotify, plist1)

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
        go (ViewIApp viewer1 viewer2) = parenthesize 9 (pprint 9 viewer1 . strstr " " . pprint 10 viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr "W_" . showsPrec 0 var . strstr "\\ " . pprint 0 viewer1)
        go (ViewTVar var) = strstr var
        go (ViewTCon con) = strstr con
        go (ViewTApp viewer1 viewer2) = parenthesize 9 (pprint 9 viewer1 . strstr " " . pprint 10 viewer2)
        go (ViewOper (oper, prec')) = case oper of
            Prefix str viewer1 -> parenthesize prec' (strstr str . pprint prec' viewer1)
            InfixL viewer1 str viewer2 -> parenthesize prec' (pprint prec' viewer1 . strstr str . pprint (prec' + 1) viewer2)
            InfixR viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint prec' viewer2)
            InfixN viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint (prec' + 1) viewer2)
        go (ViewChrL chr) = showsPrec 0 chr
        go (ViewStrL str) = showsPrec 0 str
        go (ViewNatL nat)
            | nat < 0 = parenthesize 8 (showsPrec 0 nat)
            | otherwise = showsPrec 0 nat
        go (ViewList viewers) = strstr "[" . ppunc ", " (map (pprint 5) viewers) . strstr "]"

constructViewer :: TermNode -> ViewNode
constructViewer term = fst (runIdentity (uncurry (runStateT . formatView . eraseType) (runIdentity (runStateT (makeView [] normalized) 1)))) where
    normalized :: TermNode
    normalized = rewrite NF term
    freeNames :: Set.Set LargeId
    freeNames = collectFreeNames normalized
    collectFreeNames :: TermNode -> Set.Set LargeId
    collectFreeNames (LVar (LV_Named name)) = Set.singleton name
    collectFreeNames (NApp term1 term2) = collectFreeNames term1 `Set.union` collectFreeNames term2
    collectFreeNames (NAbs body) = collectFreeNames body
    collectFreeNames _ = Set.empty
    freshBinder :: StateT Int Identity Int
    freshBinder = do
        candidate <- get
        put (candidate + 1)
        if ("W_" ++ show candidate) `Set.member` freeNames then freshBinder else return candidate
    isType :: ViewNode -> Bool
    isType (ViewTVar _) = True
    isType (ViewTCon _) = True
    isType (ViewTApp _ _) = True
    isType _ = False
    makeView :: [Int] -> TermNode -> StateT Int Identity ViewNode
    makeView vars (LVar var) = case var of
        LV_ty_var v -> return (ViewTVar ("TV_" ++ show v))
        LV_Unique v -> return (ViewLVar ("V_" ++ show v))
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
            DC_Eq -> return (ViewDCon "=")
            DC_Arith AO_Positive -> return (ViewDCon "$unary+")
            DC_Arith AO_Negate -> return (ViewDCon "$unary-")
            DC_Arith operator -> return (ViewDCon (show operator))
        TC type_constructor -> case type_constructor of
            TC_Arrow -> return (ViewTCon "->")
            TC_Unique uni -> return (ViewTCon ("tc_" ++ show uni))
            TC_Named name -> return (ViewTCon ("__" ++ name))
    makeView vars (NIdx idx) = return (ViewIVar (vars !! (idx - 1)))
    makeView vars (NApp t1 t2) = do
        t1_rep <- makeView vars t1
        t2_rep <- makeView vars t2
        return (if isType t1_rep then ViewTApp t1_rep t2_rep else ViewIApp t1_rep t2_rep)
    makeView vars (NAbs t) = do
        var <- freshBinder
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
    checkOper "is" = Just (InfixN () " is " (), 5)
    checkOper "=:=" = Just (InfixN () " =:= " (), 5)
    checkOper "=\\=" = Just (InfixN () " =\\= " (), 5)
    checkOper "<" = Just (InfixN () " < " (), 5)
    checkOper "=<" = Just (InfixN () " =< " (), 5)
    checkOper ">" = Just (InfixN () " > " (), 5)
    checkOper ">=" = Just (InfixN () " >= " (), 5)
    checkOper "+" = Just (InfixL () " + " (), 6)
    checkOper "-" = Just (InfixL () " - " (), 6)
    checkOper "*" = Just (InfixL () " * " (), 7)
    checkOper "/" = Just (InfixL () " / " (), 7)
    checkOper "//" = Just (InfixL () " // " (), 7)
    checkOper "div" = Just (InfixL () " div " (), 7)
    checkOper "mod" = Just (InfixL () " mod " (), 7)
    checkOper "rem" = Just (InfixL () " rem " (), 7)
    checkOper "$unary+" = Just (Prefix "+" (), 8)
    checkOper "$unary-" = Just (Prefix "-" (), 8)
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
                v2 <- freshBinder
                return (ViewIAbs v2 (ViewOper (InfixL t1' str (ViewIVar v2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView t1
                v2 <- freshBinder
                return (ViewIAbs v2 (ViewOper (InfixR t1' str (ViewIVar v2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView t1
                v2 <- freshBinder
                return (ViewIAbs v2 (ViewOper (InfixN t1' str (ViewIVar v2), prec)))
    formatView (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                v1 <- freshBinder
                return (ViewIAbs v1 (ViewOper (Prefix str (ViewIVar v1), prec)))
            InfixL _ str _ -> do
                v1 <- freshBinder
                v2 <- freshBinder
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixL (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixR _ str _ -> do
                v1 <- freshBinder
                v2 <- freshBinder
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixR (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixN _ str _ -> do
                v1 <- freshBinder
                v2 <- freshBinder
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixN (ViewIVar v1) str (ViewIVar v2), prec))))
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
