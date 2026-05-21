module Hol.BETA2.TermNode where

import Calc.Presburger.Internal (MyPresburgerFormulaRep, MyVar)
import Hol.BETA2.Constant
import Hol.BETA2.Header
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
    | LV_Unique Unique DispHint
    | LV_Named LargeId
    deriving (Eq, Ord)

data TermNode
    = LVar !LogicVar
    | NCon !Constant !(Maybe SLoc)
    | NIdx {-# UNPACK #-} !DeBruijn
    | NApp !TermNode !TermNode !(Maybe SLoc)
    | NLam !(Maybe SmallId) !LamType !TermNode !(Maybe SLoc)
    | Susp
        { getSuspBody :: !TermNode
        , getSuspOL :: {-# UNPACK #-} !Int
        , getSuspNL :: {-# UNPACK #-} !Int
        , getSuspEnv :: !SuspEnv
        }
    | NPresburgerCheck !MyPresburgerFormulaRep !(Map.Map MyVar LogicVar) !(Maybe SLoc)

newtype LamType = LamType { unLamType :: Maybe (MonoType Int) }

instance Eq LamType where
    _ == _ = True

instance Ord LamType where
    compare _ _ = EQ

noLamType :: LamType
noLamType = LamType Nothing

mkLamType :: MonoType Int -> LamType
mkLamType = LamType . Just

instance Eq TermNode where
    LVar v1 == LVar v2 = v1 == v2
    NCon c1 _ == NCon c2 _ = c1 == c2
    NIdx i == NIdx j = i == j
    NApp a1 b1 _ == NApp a2 b2 _ = a1 == a2 && b1 == b2
    NLam _ _ b1 _ == NLam _ _ b2 _ = b1 == b2
    Susp b1 ol1 nl1 e1 == Susp b2 ol2 nl2 e2 = b1 == b2 && ol1 == ol2 && nl1 == nl2 && e1 == e2
    NPresburgerCheck f1 m1 _ == NPresburgerCheck f2 m2 _ = f1 == f2 && m1 == m2
    _ == _ = False

instance Ord TermNode where
    compare = cmpTerm
      where
        ctorIdx :: TermNode -> Int
        ctorIdx (LVar _) = 0
        ctorIdx (NCon _ _) = 1
        ctorIdx (NIdx _) = 2
        ctorIdx (NApp _ _ _) = 3
        ctorIdx (NLam _ _ _ _) = 4
        ctorIdx (Susp {}) = 5
        ctorIdx (NPresburgerCheck _ _ _) = 6
        cmpTerm :: TermNode -> TermNode -> Ordering
        cmpTerm (LVar v1) (LVar v2) = compare v1 v2
        cmpTerm (NCon c1 _) (NCon c2 _) = compare c1 c2
        cmpTerm (NIdx i) (NIdx j) = compare i j
        cmpTerm (NApp a1 b1 _) (NApp a2 b2 _) = compare a1 a2 <> compare b1 b2
        cmpTerm (NLam _ _ b1 _) (NLam _ _ b2 _) = compare b1 b2
        cmpTerm (Susp b1 ol1 nl1 e1) (Susp b2 ol2 nl2 e2) =
            compare b1 b2 <> compare ol1 ol2 <> compare nl1 nl2 <> compare e1 e2
        cmpTerm (NPresburgerCheck f1 m1 _) (NPresburgerCheck f2 m2 _) =
            compare f1 f2 <> compare m1 m2
        cmpTerm a b = compare (ctorIdx a) (ctorIdx b)

data SuspItem
    = Dummy {-# UNPACK #-} !Int
    | Binds TermNode {-# UNPACK #-} !Int
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
    = ViewIVar SmallId
    | ViewLVar LargeId
    | ViewDCon SmallId
    | ViewIApp ViewNode ViewNode
    | ViewIAbs SmallId ViewNode
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
        go (ViewIVar var) = strstr var
        go (ViewLVar var) = strstr var
        go (ViewDCon con) = strstr con
        go (ViewIApp viewer1 viewer2) = parenthesize 6 (pprint 6 viewer1 . strstr " " . pprint 7 viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr var . strstr "\\ " . pprint 0 viewer1)
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
    showsPrec prec (LV_Unique uni (DispHint mhint)) = case mhint of
        Just s -> strstr s
        Nothing -> strstr "?V_" . showsPrec prec (unUnique uni)
    showsPrec prec (LV_Named name) = strstr name

{-# INLINE mkLVar #-}
mkLVar :: LogicVar -> TermNode
mkLVar v = LVar v

mkNCon :: ToConstant a => a -> TermNode
mkNCon = go . makeConstant where
    go :: Constant -> TermNode
    go c = NCon c Nothing

{-# INLINE mkNConLoc #-}
mkNConLoc :: ToConstant a => Maybe SLoc -> a -> TermNode
mkNConLoc sl x = NCon (makeConstant x) sl

{-# INLINE mkNIdx #-}
mkNIdx :: DeBruijn -> TermNode
mkNIdx i = NIdx i

{-# INLINABLE mkNApp #-}
mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (NCon (DC (DC_Succ)) _) (NCon (DC (DC_NatL n)) _)
    = n' `seq` mkNCon (DC_NatL n')
    where
        n' = n + 1
mkNApp t1 t2 = NApp t1 t2 Nothing

{-# INLINE mkNAppLoc #-}
mkNAppLoc :: Maybe SLoc -> TermNode -> TermNode -> TermNode
mkNAppLoc sl (NCon (DC (DC_Succ)) _) (NCon (DC (DC_NatL n)) _)
    = n' `seq` mkNConLoc sl (DC_NatL n')
    where
        n' = n + 1
mkNAppLoc sl t1 t2 = NApp t1 t2 sl

{-# INLINE mkNLam #-}
mkNLam :: TermNode -> TermNode
mkNLam t = NLam Nothing noLamType t Nothing

{-# INLINE mkNLamHint #-}
mkNLamHint :: Maybe SmallId -> TermNode -> TermNode
mkNLamHint h t = NLam h noLamType t Nothing

{-# INLINE mkNLamHintTy #-}
mkNLamHintTy :: Maybe SmallId -> LamType -> TermNode -> TermNode
mkNLamHintTy h ty t = NLam h ty t Nothing

{-# INLINE mkNLamLoc #-}
mkNLamLoc :: Maybe SLoc -> Maybe SmallId -> LamType -> TermNode -> TermNode
mkNLamLoc sl h ty t = NLam h ty t sl

getNodeSLoc :: TermNode -> Maybe SLoc
getNodeSLoc (NCon _ sl) = sl
getNodeSLoc (NApp _ _ sl) = sl
getNodeSLoc (NLam _ _ _ sl) = sl
getNodeSLoc (NPresburgerCheck _ _ sl) = sl
getNodeSLoc _ = Nothing

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

substTyMTV :: MetaTVar -> Unique -> TermNode -> TermNode
substTyMTV mtv uni = go where
    refTy :: MonoType Int
    refTy = TyCon (TCon (TC_Unique uni) Star)
    go :: TermNode -> TermNode
    go (NApp t1 t2 sl) = mkNAppLoc sl (go t1) (go t2)
    go (NLam h ty t sl) = mkNLamLoc sl h (goLamType ty) (go t)
    go (Susp t ol nl env) = mkSusp (go t) ol nl (map goItem env)
    go t = t
    goItem :: SuspItem -> SuspItem
    goItem (Dummy n) = Dummy n
    goItem (Binds t n) = Binds (go t) n
    goLamType :: LamType -> LamType
    goLamType (LamType (Just ty)) = LamType (Just (goMono ty))
    goLamType x = x
    goMono :: MonoType Int -> MonoType Int
    goMono (TyMTV m)
        | m == mtv = refTy
        | otherwise = TyMTV m
    goMono (TyApp a b) = TyApp (goMono a) (goMono b)
    goMono t = t

rewriteWithSusp :: TermNode -> Int -> Int -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSusp t ol nl env option = dispatch t where
    dispatch :: TermNode -> TermNode
    dispatch (LVar {})
        = t
    dispatch (NIdx i)
        | i >= ol = if ol == nl then t else mkNIdx (i - ol + nl)
        | i >= 0 = case env !! i of
            Dummy l -> mkNIdx (nl - l)
            Binds t' l -> rewriteWithSusp t' 0 (nl - l) [] option
        | otherwise = error "***normalizeWithSuspEnv: A negative De-Bruijn index given..."
    dispatch (NCon {})
        = t
    dispatch (NApp t1 t2 sl)
        | NLam _ _ t11 _ <- t1' = beta t11
        | option == WHNF = mkNAppLoc sl t1' (mkSusp t2 ol nl env)
        | option == HNF = mkNAppLoc sl (rewriteWithSusp t1' 0 0 [] option) (mkSusp t2 ol nl env)
        | option == NF = mkNAppLoc sl (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
        where
            t1' :: TermNode
            t1' = rewriteWithSusp t1 ol nl env WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' ol' nl' (Dummy l' : env'))
                | nl' == l' = rewriteWithSusp t' ol' (pred nl') (mkBinds (mkSusp t2 ol nl env) (pred l') : env') option
            beta t' = rewriteWithSusp t' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
    dispatch (NLam h ty t1 sl)
        | option == WHNF = mkNLamLoc sl h ty (mkSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
        | otherwise = mkNLamLoc sl h ty (rewriteWithSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option)
    dispatch (Susp t' ol' nl' env')
        | ol' == 0 && nl' == 0 = rewriteWithSusp t' ol nl env option
        | ol == 0 = rewriteWithSusp t' ol' (nl + nl') env' option
        | otherwise = rewriteWithSusp (rewriteWithSusp t' ol' nl' env' WHNF) ol nl env option
    dispatch (NPresburgerCheck {})
        = t

{-# INLINE rewrite #-}
rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = case t of
    LVar {} -> t
    NCon {} -> t
    NIdx {} -> t
    NPresburgerCheck {} -> t
    _ -> rewriteWithSusp t 0 0 [] option

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NCon (DC (DC_NatL n)) _) ts
        | n == 0 = (mkNCon (DC_NatL 0), ts)
        | n > 0 = n' `seq` (mkNCon DC_Succ, mkNCon (DC_NatL n') : ts)
        | otherwise = error "`unfoldlNApp\': negative integer"
        where
            n' = n - 1
    go (NApp t1 t2 _) ts = go t1 (t2 : ts)
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

makeNestedNLamH :: [Maybe SmallId] -> TermNode -> TermNode
makeNestedNLamH [] t = t
makeNestedNLamH (h : hs) t = mkNLamHint h (makeNestedNLamH hs t)

freshenName :: SmallId -> [SmallId] -> SmallId
freshenName h live
    | h `notElem` live = h
    | otherwise = pickFresh
  where
    isDigitChar c = c >= '0' && c <= '9'
    rev_rest = dropWhile isDigitChar (reverse h)
    base = if null rev_rest then h else reverse rev_rest
    pickFresh = go (1 :: Int)
    go i
        | cand `notElem` live = cand
        | otherwise = go (i + 1)
        where
            cand = base ++ show i

viewNestedNLam :: TermNode -> (Int, TermNode)
viewNestedNLam = go 0 where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NLam _ _ t _) = go (n + 1) t
    go n t = (n, t)

viewNestedNLamH :: TermNode -> ([Maybe SmallId], TermNode)
viewNestedNLamH = go [] where
    go :: [Maybe SmallId] -> TermNode -> ([Maybe SmallId], TermNode)
    go hs (NLam h _ t _) = go (h : hs) t
    go hs t = (reverse hs, t)

constructViewer :: TermNode -> ViewNode
constructViewer = constructViewerWith (const Nothing)

constructViewerWith :: (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerWith = constructViewerCustom defaultCheckOper

defaultCheckOper :: String -> Maybe (Fixity (), Precedence)
defaultCheckOper "->" = Just (InfixR () " -> " (), 4)
defaultCheckOper "::" = Just (InfixR () " :: " (), 4)
defaultCheckOper "Lambda" = Just (Prefix "Lambda " (), 0)
defaultCheckOper ":-" = Just (InfixR () " :- " (), 0)
defaultCheckOper ";" = Just (InfixL () "; " (), 1)
defaultCheckOper "&" = Just (InfixL () " & " (), 3)
defaultCheckOper "=>" = Just (InfixR () " => " (), 2)
defaultCheckOper "pi" = Just (Prefix "pi " (), 5)
defaultCheckOper "sigma" = Just (Prefix "sigma " (), 5)
defaultCheckOper "=" = Just (InfixN () " = " (), 5)
defaultCheckOper "=<" = Just (InfixN () " =< " (), 5)
defaultCheckOper "<" = Just (InfixN () " < " (), 5)
defaultCheckOper ">=" = Just (InfixN () " >= " (), 5)
defaultCheckOper ">" = Just (InfixN () " > " (), 5)
defaultCheckOper "is" = Just (InfixN () " is " (), 5)
defaultCheckOper "+" = Just (InfixN () " + " (), 6)
defaultCheckOper "-" = Just (InfixN () " - " (), 6)
defaultCheckOper "*" = Just (InfixN () " * " (), 7)
defaultCheckOper "/" = Just (InfixN () " / " (), 7)
defaultCheckOper _ = Nothing

constructViewerCustom :: (String -> Maybe (Fixity (), Precedence)) -> (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerCustom checkOper lookupName = fst . runIdentity . uncurry (runStateT . formatView . eraseType) . runIdentity . flip runStateT 1 . makeView [] . rewrite NF where
    isType :: ViewNode -> Bool
    isType (ViewTVar _) = True
    isType (ViewTCon _) = True
    isType (ViewTApp _ _) = True
    isType _ = False
    makeView :: [SmallId] -> TermNode -> StateT Int Identity ViewNode
    makeView vars (LVar var) = case var of
        LV_ty_var v -> return (ViewTVar ("?TV_" ++ show v))
        LV_Unique v (DispHint mhint) -> return (ViewLVar (case lookupName var of
            Just cached -> cached
            Nothing -> case mhint of
                Just s -> s
                Nothing -> "?V_" ++ show v))
        LV_Named v -> return (ViewLVar (case lookupName var of
            Just cached -> cached
            Nothing -> v))
    makeView vars (NCon con _) = case con of
        DC data_constructor -> case data_constructor of
            DC_LO logical_operator -> return (ViewDCon (show logical_operator))
            DC_Named name -> return (ViewDCon ("__" ++ name))
            DC_Unique uni (DispHint mhint) -> return (ViewDCon (case mhint of Just s -> s; Nothing -> "c_" ++ show uni))
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
    makeView vars (NApp t1 t2 _) = do
        t1_rep <- makeView vars t1
        t2_rep <- makeView vars t2
        return (if isType t1_rep then ViewTApp t1_rep t2_rep else ViewIApp t1_rep t2_rep)
    makeView vars (NLam mhint _ t _) = do
        counter <- get
        put (counter + 1)
        let preferred = case mhint of
                Just s -> s
                Nothing -> "W_" ++ show counter
            chosen = freshenName preferred vars
        t_rep <- makeView (chosen : vars) t
        return (ViewIAbs chosen t_rep)
    makeView vars (NPresburgerCheck rep _ _) =
        return (ViewDCon ("presburger \"" ++ shows rep "\""))
    makeView vars (Susp body _ _ _) = makeView vars body
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
                let n2 = "W_" ++ show v2
                return (ViewIAbs n2 (ViewOper (InfixL t1' str (ViewIVar n2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                let n2 = "W_" ++ show v2
                return (ViewIAbs n2 (ViewOper (InfixR t1' str (ViewIVar n2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView t1
                v2 <- get
                let v2' = v2 + 1
                v2' `seq` put v2'
                let n2 = "W_" ++ show v2
                return (ViewIAbs n2 (ViewOper (InfixN t1' str (ViewIVar n2), prec)))
    formatView (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                v1 <- get
                put (v1 + 1)
                let n1 = "W_" ++ show v1
                return (ViewIAbs n1 (ViewOper (Prefix str (ViewIVar n1), prec)))
            InfixL _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                let n1 = "W_" ++ show v1
                    n2 = "W_" ++ show v2
                return (ViewIAbs n1 (ViewIAbs n2 (ViewOper (InfixL (ViewIVar n1) str (ViewIVar n2), prec))))
            InfixR _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                let n1 = "W_" ++ show v1
                    n2 = "W_" ++ show v2
                return (ViewIAbs n1 (ViewIAbs n2 (ViewOper (InfixR (ViewIVar n1) str (ViewIVar n2), prec))))
            InfixN _ str _ -> do
                v1 <- get
                let v2 = v1 + 1
                put (v2 + 1)
                let n1 = "W_" ++ show v1
                    n2 = "W_" ++ show v2
                return (ViewIAbs n1 (ViewIAbs n2 (ViewIAbs n2 (ViewOper (InfixN (ViewIVar n1) str (ViewIVar n2), prec)))))
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
