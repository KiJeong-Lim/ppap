module Hol.ALPHA2.TermNode where

import Hol.ALPHA2.Constant
import Hol.ALPHA2.Header
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
    = LVar !LogicVar
    | NCon !Constant
    | NIdx {-# UNPACK #-} !DeBruijn
    | NApp !TermNode !TermNode
    | NLam !TermNode
    | Susp { getSuspBody :: !TermNode , getSuspOL :: {-# UNPACK #-} !Int , getSuspNL :: {-# UNPACK #-} !Int , getSuspEnv :: !SuspEnv }
    deriving ()

data SuspItem
    = Dummy {-# UNPACK #-} !Int
    | Binds TermNode {-# UNPACK #-} !Int
    deriving ()

-- Force the semantic-domain invariant at API boundaries which inspect a
-- complete term.  The raw constructor remains available for internal tests,
-- so consumers must not reinterpret a forged negative index as an ordinary
-- term or a recoverable failure.
assertNonnegativeIndices :: TermNode -> ()
assertNonnegativeIndices term = case term of
    LVar _ -> ()
    NCon _ -> ()
    NIdx i
        | i >= 0 -> ()
        | otherwise -> undefined
    NApp t1 t2 -> assertNonnegativeIndices t1 `seq` assertNonnegativeIndices t2
    NLam body -> assertNonnegativeIndices body
    Susp body _ _ env -> assertNonnegativeIndices body `seq` assertNonnegativeSuspEnv env

assertNonnegativeTerms :: [TermNode] -> ()
assertNonnegativeTerms [] = ()
assertNonnegativeTerms (term : rest) = assertNonnegativeIndices term `seq` assertNonnegativeTerms rest

assertNonnegativeSuspEnv :: SuspEnv -> ()
assertNonnegativeSuspEnv [] = ()
assertNonnegativeSuspEnv (Dummy _ : rest) = assertNonnegativeSuspEnv rest
assertNonnegativeSuspEnv (Binds body _ : rest) = assertNonnegativeIndices body `seq` assertNonnegativeSuspEnv rest

assertNonnegativeSuspItem :: SuspItem -> ()
assertNonnegativeSuspItem (Dummy _) = ()
assertNonnegativeSuspItem (Binds body _) = assertNonnegativeIndices body

instance Eq SuspItem where
    lhs == rhs
        = assertNonnegativeSuspItem lhs `seq`
          assertNonnegativeSuspItem rhs `seq`
          case (lhs, rhs) of
            (Dummy l1, Dummy l2) -> l1 == l2
            (Binds t1 l1, Binds t2 l2) -> t1 == t2 && l1 == l2
            _ -> False

instance Ord SuspItem where
    compare lhs rhs
        = assertNonnegativeSuspItem lhs `seq`
          assertNonnegativeSuspItem rhs `seq`
          case (lhs, rhs) of
            (Dummy l1, Dummy l2) -> compare l1 l2
            (Dummy _, Binds _ _) -> LT
            (Binds _ _, Dummy _) -> GT
            (Binds t1 l1, Binds t2 l2) -> compare t1 t2 <> compare l1 l2

instance Eq TermNode where
    lhs == rhs
        = assertNonnegativeIndices lhs `seq`
          assertNonnegativeIndices rhs `seq`
          eqTerm lhs rhs
      where
        eqTerm (LVar v1) (LVar v2) = v1 == v2
        eqTerm (NCon c1) (NCon c2) = c1 == c2
        eqTerm (NIdx i) (NIdx j) = i == j
        eqTerm (NApp a1 b1) (NApp a2 b2) = eqTerm a1 a2 && eqTerm b1 b2
        eqTerm (NLam b1) (NLam b2) = eqTerm b1 b2
        eqTerm (Susp b1 ol1 nl1 e1) (Susp b2 ol2 nl2 e2) = eqTerm b1 b2 && ol1 == ol2 && nl1 == nl2 && e1 == e2
        eqTerm _ _ = False

instance Ord TermNode where
    compare lhs rhs
        = assertNonnegativeIndices lhs `seq`
          assertNonnegativeIndices rhs `seq`
          cmpTerm lhs rhs
      where
        ctorIdx :: TermNode -> Int
        ctorIdx (LVar _) = 0
        ctorIdx (NCon _) = 1
        ctorIdx (NIdx i)
            | i >= 0 = 2
            | otherwise = undefined
        ctorIdx (NApp _ _) = 3
        ctorIdx (NLam _) = 4
        ctorIdx (Susp {}) = 5
        cmpTerm :: TermNode -> TermNode -> Ordering
        cmpTerm (LVar v1) (LVar v2) = compare v1 v2
        cmpTerm (NCon c1) (NCon c2) = compare c1 c2
        cmpTerm (NIdx i) (NIdx j)
            | i < 0 || j < 0 = undefined
            | otherwise = compare i j
        cmpTerm (NApp a1 b1) (NApp a2 b2) = cmpTerm a1 a2 <> cmpTerm b1 b2
        cmpTerm (NLam b1) (NLam b2) = cmpTerm b1 b2
        cmpTerm (Susp b1 ol1 nl1 e1) (Susp b2 ol2 nl2 e2) =
            cmpTerm b1 b2 <> compare ol1 ol2 <> compare nl1 nl2 <> compare e1 e2
        cmpTerm a b = compare (ctorIdx a) (ctorIdx b)

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
        sameLevelOperand :: (Fixity ViewNode -> Bool) -> Precedence -> ViewNode -> String -> String
        sameLevelOperand compatible prec' viewer = case viewer of
            ViewOper (oper', viewer_prec)
                | viewer_prec == prec'
                , not (compatible oper')
                -> strstr "(" . pprint 0 viewer . strstr ")"
            _ -> pprint prec' viewer
        isInfixL :: Fixity ViewNode -> Bool
        isInfixL (InfixL _ _ _) = True
        isInfixL _ = False
        isInfixR :: Fixity ViewNode -> Bool
        isInfixR (InfixR _ _ _) = True
        isInfixR _ = False
        go :: ViewNode -> String -> String
        go (ViewIVar var) = strstr "W_" . showsPrec 0 var
        go (ViewLVar var) = strstr var
        go (ViewDCon con) = strstr con
        go (ViewIApp viewer1 viewer2) = parenthesize appViewPrec (pprint appViewPrec viewer1 . strstr " " . pprint (appViewPrec + 1) viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr "W_" . showsPrec 0 var . strstr "\\ " . pprint 0 viewer1)
        go (ViewTVar var) = strstr var
        go (ViewTCon con) = strstr con
        go (ViewTApp viewer1 viewer2) = parenthesize appViewPrec (pprint appViewPrec viewer1 . strstr " " . pprint (appViewPrec + 1) viewer2)
        go (ViewOper (oper, prec')) = case oper of
            Prefix str viewer1 -> parenthesize prec' (strstr str . pprint prec' viewer1)
            InfixL viewer1 str viewer2 -> parenthesize prec' (sameLevelOperand isInfixL prec' viewer1 . strstr str . pprint (prec' + 1) viewer2)
            InfixR viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . sameLevelOperand isInfixR prec' viewer2)
            InfixN viewer1 str viewer2 -> parenthesize prec' (pprint (prec' + 1) viewer1 . strstr str . pprint (prec' + 1) viewer2)
        go (ViewChrL chr) = showsPrec 0 chr
        go (ViewStrL str) = showsPrec 0 str
        go (ViewNatL nat) = showsPrec 0 nat
        go (ViewList viewers) = strstr "[" . ppunc ", " (map (pprint 6) viewers) . strstr "]"

instance Show LogicVar where
    showsPrec prec (LV_ty_var uni) = strstr "?TV_" . showsPrec prec (unUnique uni)
    showsPrec prec (LV_Unique uni) = strstr "?LV_" . showsPrec prec (unUnique uni)
    showsPrec prec (LV_Named name) = strstr name

{-# INLINE mkLVar #-}
mkLVar :: LogicVar -> TermNode
mkLVar v = LVar v

mkNCon :: ToConstant a => a -> TermNode
mkNCon = go . makeConstant where
    go :: Constant -> TermNode
    go c = NCon c

{-# INLINE mkNIdx #-}
mkNIdx :: DeBruijn -> TermNode
mkNIdx i
    | i >= 0 = NIdx i
    | otherwise = undefined

{-# INLINABLE mkNApp #-}
mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (NCon (DC (DC_Succ))) (NCon (DC (DC_NatL n)))
    = n' `seq` mkNCon (DC_NatL n')
    where
        n' = n + 1
mkNApp t1 t2
    = NApp t1 t2

{-# INLINE mkNLam #-}
mkNLam :: TermNode -> TermNode
mkNLam t = NLam t

{-# INLINE mkSusp #-}
mkSusp :: TermNode -> Int -> Int -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl env = Susp { getSuspBody = t, getSuspOL = ol, getSuspNL = nl, getSuspEnv = env }

{-# INLINE mkDummy #-}
mkDummy :: Int -> SuspItem
mkDummy l = Dummy l

{-# INLINE mkBinds #-}
mkBinds :: TermNode -> Int -> SuspItem
mkBinds t l = Binds t l

rewriteWithSusp :: TermNode -> Int -> Int -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSusp t ol nl env option
    = assertNonnegativeIndices t `seq`
        assertNonnegativeSuspEnv env `seq`
        rewriteWithSuspUnchecked t ol nl env option

rewriteWithSuspUnchecked :: TermNode -> Int -> Int -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSuspUnchecked t ol nl env option = dispatch t where
    dispatch :: TermNode -> TermNode
    dispatch (LVar {})
        = t
    dispatch (NIdx i)
        | i < 0 = undefined
        | i >= ol = if ol == nl then t else mkNIdx (i - ol + nl)
        | i >= 0 = case drop i env of
            Dummy l : _ -> mkNIdx (nl - l)
            Binds t' l : _ -> rewriteWithSuspUnchecked t' 0 (nl - l) [] option
            [] -> undefined
        | otherwise = undefined
    dispatch (NCon {})
        = t
    dispatch (NApp t1 t2)
        | NLam t11 <- t1' = beta t11
        | option == WHNF = mkNApp t1' (mkSusp t2 ol nl env)
        | option == HNF = mkNApp (rewriteWithSuspUnchecked t1' 0 0 [] option) (mkSusp t2 ol nl env)
        | option == NF = mkNApp (rewriteWithSuspUnchecked t1' 0 0 [] option) (rewriteWithSuspUnchecked t2 ol nl env option)
        where
            t1' :: TermNode
            t1' = rewriteWithSuspUnchecked t1 ol nl env WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' ol' nl' (Dummy l' : env'))
                | nl' == l' = rewriteWithSuspUnchecked t' ol' (pred nl') (mkBinds (mkSusp t2 ol nl env) (pred l') : env') option
            beta t' = rewriteWithSuspUnchecked t' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
    dispatch (NLam t1)
        | option == WHNF = mkNLam (mkSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
        | otherwise = mkNLam (rewriteWithSuspUnchecked t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option)
    dispatch (Susp t' ol' nl' env')
        | ol' == 0 && nl' == 0 = rewriteWithSuspUnchecked t' ol nl env option
        | ol == 0 = rewriteWithSuspUnchecked t' ol' (nl + nl') env' option
        | otherwise = rewriteWithSuspUnchecked (rewriteWithSuspUnchecked t' ol' nl' env' WHNF) ol nl env option

{-# INLINE rewrite #-}
rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = assertNonnegativeIndices t `seq` case t of
    LVar {} -> t
    NCon {} -> t
    NIdx i
        | i >= 0 -> t
        | otherwise -> undefined
    _ -> rewriteWithSuspUnchecked t 0 0 [] option

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp term = assertNonnegativeIndices term `seq` go term [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go t@(NCon (DC (DC_NatL n))) ts
        | n == 0 = (mkNCon (DC_NatL 0), ts)
        | n > 0 = n' `seq` (mkNCon DC_Succ, mkNCon (DC_NatL n') : ts)
        | otherwise = (t, ts)
        where
            n' = n - 1
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
viewNestedNLam term = assertNonnegativeIndices term `seq` go 0 term where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NLam t) = go (n + 1) t
    go n t = (n, t)

constructViewer :: TermNode -> ViewNode
constructViewer term = fst . runIdentity $ runStateT (formatView rendered_names (eraseType raw_view)) next_fresh where
    normalized :: TermNode
    normalized = rewrite NF term
    raw_view :: ViewNode
    next_fresh :: Int
    (raw_view, next_fresh) = runIdentity (runStateT (makeView [] normalized) 1)
    free_names :: Set.Set SmallId
    free_names = collectFreeNames normalized
    rendered_names :: Set.Set SmallId
    rendered_names = collectViewNames raw_view
    collectFreeNames :: TermNode -> Set.Set SmallId
    collectFreeNames (LVar var) = case var of
        LV_Named name -> Set.singleton name
        _ -> Set.empty
    collectFreeNames (NCon (DC (DC_Named name))) = Set.singleton name
    collectFreeNames (NCon {}) = Set.empty
    collectFreeNames (NIdx i)
        | i >= 0 = Set.empty
        | otherwise = undefined
    collectFreeNames (NApp t1 t2) = Set.union (collectFreeNames t1) (collectFreeNames t2)
    collectFreeNames (NLam t) = collectFreeNames t
    collectFreeNames (Susp body _ _ env) = Set.unions (collectFreeNames body : map collectItemNames env) where
        collectItemNames (Dummy _) = Set.empty
        collectItemNames (Binds t _) = collectFreeNames t
    collectViewNames :: ViewNode -> Set.Set SmallId
    collectViewNames viewer = case viewer of
        ViewIVar var -> Set.singleton ("W_" ++ show var)
        ViewLVar var -> Set.singleton var
        ViewDCon ('_' : '_' : con) -> Set.singleton con
        ViewDCon con -> Set.singleton con
        ViewIApp t1 t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
        ViewIAbs var t -> Set.insert ("W_" ++ show var) (collectViewNames t)
        ViewTVar var -> Set.singleton var
        ViewTCon ('_' : '_' : con) -> Set.singleton con
        ViewTCon con -> Set.singleton con
        ViewTApp t1 t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
        ViewOper (oper, _) -> case oper of
            Prefix _ t -> collectViewNames t
            InfixL t1 _ t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
            InfixR t1 _ t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
            InfixN t1 _ t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
        ViewNatL _ -> Set.empty
        ViewChrL _ -> Set.empty
        ViewStrL _ -> Set.empty
        ViewList ts -> Set.unions (map collectViewNames ts)
    freshViewIndex :: Set.Set SmallId -> StateT Int Identity Int
    freshViewIndex forbidden = do
        candidate0 <- get
        let pick candidate
                | Set.member ("W_" ++ show candidate) forbidden = pick (candidate + 1)
                | otherwise = candidate
            candidate = pick candidate0
        put (candidate + 1)
        return candidate
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
    makeView vars (NIdx idx)
        | idx < 0 = undefined
        | var : _ <- drop idx vars = return (ViewIVar var)
        | otherwise = undefined
    makeView vars (NApp t1 t2) = do
        t1_rep <- makeView vars t1
        t2_rep <- makeView vars t2
        return (if isType t1_rep then ViewTApp t1_rep t2_rep else ViewIApp t1_rep t2_rep)
    makeView vars (NLam t) = do
        var <- freshViewIndex free_names
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
    checkOper ":-" = Just (InfixN () " :- " (), 0)
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
    checkOper "+" = Just (InfixL () " + " (), 6)
    checkOper "-" = Just (InfixL () " - " (), 6)
    checkOper "*" = Just (InfixL () " * " (), 7)
    checkOper "/" = Just (InfixL () " / " (), 7)
    checkOper _ = Nothing
    formatView :: Set.Set SmallId -> ViewNode -> StateT Int Identity ViewNode
    formatView _ (ViewDCon "[]") = return (ViewList [])
    formatView forbidden (ViewIApp (ViewIApp (ViewDCon "::") (ViewChrL chr)) t) = do
        t' <- formatView forbidden t
        case t' of
            ViewStrL str -> return (ViewStrL (chr : str))
            t' -> return (ViewOper (InfixR (ViewChrL chr) " :: " t', 4))
    formatView forbidden (ViewIApp (ViewIApp (ViewDCon "::") t1) t2) = do
        t1' <- formatView forbidden t1
        t2' <- formatView forbidden t2
        case t2' of
            ViewList ts -> return (ViewList (t1' : ts))
            _ -> return (ViewOper (InfixR t1' " :: " t2', 4))
    formatView forbidden (ViewIApp (ViewIApp (ViewDCon con) t1) t2)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView forbidden t1
                t2' <- formatView forbidden t2
                return (ViewIApp (ViewOper (Prefix str t1', prec)) t2')
            InfixL _ str _ -> do
                t1' <- formatView forbidden t1
                t2' <- formatView forbidden t2
                return (ViewOper (InfixL t1' str t2', prec))
            InfixR _ str _ -> do
                t1' <- formatView forbidden t1
                t2' <- formatView forbidden t2
                return (ViewOper (InfixR t1' str t2', prec))
            InfixN _ str _ -> do
                t1' <- formatView forbidden t1
                t2' <- formatView forbidden t2
                return (ViewOper (InfixN t1' str t2', prec))
    formatView forbidden (ViewIApp (ViewDCon con) t1)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                t1' <- formatView forbidden t1
                return (ViewOper (Prefix str t1', prec))
            InfixL _ str _ -> do
                t1' <- formatView forbidden t1
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v2 (ViewOper (InfixL t1' str (ViewIVar v2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView forbidden t1
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v2 (ViewOper (InfixR t1' str (ViewIVar v2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView forbidden t1
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v2 (ViewOper (InfixN t1' str (ViewIVar v2), prec)))
    formatView forbidden (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                v1 <- freshViewIndex forbidden
                return (ViewIAbs v1 (ViewOper (Prefix str (ViewIVar v1), prec)))
            InfixL _ str _ -> do
                v1 <- freshViewIndex forbidden
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixL (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixR _ str _ -> do
                v1 <- freshViewIndex forbidden
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixR (ViewIVar v1) str (ViewIVar v2), prec))))
            InfixN _ str _ -> do
                v1 <- freshViewIndex forbidden
                v2 <- freshViewIndex forbidden
                return (ViewIAbs v1 (ViewIAbs v2 (ViewOper (InfixN (ViewIVar v1) str (ViewIVar v2), prec))))
    formatView forbidden (ViewTApp (ViewTApp (ViewTCon "->") t1) t2) = do
        t1' <- formatView forbidden t1
        t2' <- formatView forbidden t2
        return (ViewOper (InfixR t1' " -> " t2', 4))
    formatView forbidden (ViewIApp t1 t2) = do
        t1' <- formatView forbidden t1
        t2' <- formatView forbidden t2
        return (ViewIApp t1' t2')
    formatView forbidden (ViewTApp t1 t2) = do
        t1' <- formatView forbidden t1
        t2' <- formatView forbidden t2
        return (ViewTApp t1' t2')
    formatView forbidden (ViewIAbs v1 t2) = do
        t2' <- formatView forbidden t2
        return (ViewIAbs v1 t2')
    formatView _ (ViewDCon ('_' : '_' : c)) = return (ViewDCon c)
    formatView _ (ViewTCon ('_' : '_' : c)) = return (ViewTCon c)
    formatView _ viewer = return viewer

appViewPrec :: Precedence
appViewPrec = 10
