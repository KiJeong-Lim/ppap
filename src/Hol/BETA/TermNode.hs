module Hol.BETA.TermNode where

import Calc.Presburger.Internal (MyPresburgerFormulaRep, MyVar, PresburgerFormula (..), PresburgerTermRep (..), showsMyVar)
import Hol.BETA.Constant
import Hol.BETA.Header
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
    | Susp { getSuspBody :: !TermNode , getSuspOL :: {-# UNPACK #-} !Int , getSuspNL :: {-# UNPACK #-} !Int , getSuspEnv :: !SuspEnv }
    | NPresburgerCheck !MyPresburgerFormulaRep !(Map.Map MyVar TermNode) !(Maybe SLoc)
    deriving ()

newtype LamType
    = LamType { unLamType :: Maybe (MonoType Int) }
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
    NCon _ _ -> ()
    NIdx i
        | i >= 0 -> ()
        | otherwise -> undefined
    NApp t1 t2 _ -> assertNonnegativeIndices t1 `seq` assertNonnegativeIndices t2
    NLam _ _ body _ -> assertNonnegativeIndices body
    Susp body _ _ env -> assertNonnegativeIndices body `seq` assertNonnegativeSuspEnv env
    NPresburgerCheck _ freeOf _ -> assertNonnegativeTerms (Map.elems freeOf)

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

instance Eq LamType where
    _ == _ = True

instance Ord LamType where
    compare _ _ = EQ

instance Eq TermNode where
    lhs == rhs
        = assertNonnegativeIndices lhs `seq`
          assertNonnegativeIndices rhs `seq`
          eqTerm lhs rhs
      where
        eqTerm (LVar v1) (LVar v2) = v1 == v2
        eqTerm (NCon c1 _) (NCon c2 _) = c1 == c2
        eqTerm (NIdx i) (NIdx j) = i == j
        eqTerm (NApp a1 b1 _) (NApp a2 b2 _) = eqTerm a1 a2 && eqTerm b1 b2
        eqTerm (NLam _ _ b1 _) (NLam _ _ b2 _) = eqTerm b1 b2
        eqTerm (Susp b1 ol1 nl1 e1) (Susp b2 ol2 nl2 e2) = eqTerm b1 b2 && ol1 == ol2 && nl1 == nl2 && e1 == e2
        eqTerm (NPresburgerCheck f1 m1 _) (NPresburgerCheck f2 m2 _) = f1 == f2 && m1 == m2
        eqTerm _ _ = False

instance Ord TermNode where
    compare lhs rhs
        = assertNonnegativeIndices lhs `seq`
          assertNonnegativeIndices rhs `seq`
          cmpTerm lhs rhs
      where
        ctorIdx :: TermNode -> Int
        ctorIdx (LVar _) = 0
        ctorIdx (NCon _ _) = 1
        ctorIdx (NIdx i)
            | i >= 0 = 2
            | otherwise = undefined
        ctorIdx (NApp _ _ _) = 3
        ctorIdx (NLam _ _ _ _) = 4
        ctorIdx (Susp {}) = 5
        ctorIdx (NPresburgerCheck _ _ _) = 6
        cmpTerm :: TermNode -> TermNode -> Ordering
        cmpTerm (LVar v1) (LVar v2) = compare v1 v2
        cmpTerm (NCon c1 _) (NCon c2 _) = compare c1 c2
        cmpTerm (NIdx i) (NIdx j)
            | i < 0 || j < 0 = undefined
            | otherwise = compare i j
        cmpTerm (NApp a1 b1 _) (NApp a2 b2 _) = cmpTerm a1 a2 <> cmpTerm b1 b2
        cmpTerm (NLam _ _ b1 _) (NLam _ _ b2 _) = cmpTerm b1 b2
        cmpTerm (Susp b1 ol1 nl1 e1) (Susp b2 ol2 nl2 e2) =
            cmpTerm b1 b2 <> compare ol1 ol2 <> compare nl1 nl2 <> compare e1 e2
        cmpTerm (NPresburgerCheck f1 m1 _) (NPresburgerCheck f2 m2 _) =
            compare f1 f2 <> compare m1 m2
        cmpTerm a b = compare (ctorIdx a) (ctorIdx b)

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
        go (ViewIVar var) = strstr var
        go (ViewLVar var) = strstr var
        go (ViewDCon con) = strstr con
        go (ViewIApp viewer1 viewer2) = parenthesize appViewPrec (pprint appViewPrec viewer1 . strstr " " . pprint (appViewPrec + 1) viewer2)
        go (ViewIAbs var viewer1) = parenthesize 0 (strstr var . strstr "\\ " . pprint 0 viewer1)
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
    showsPrec prec (LV_Unique uni (DispHint mhint)) = maybe (strstr "?V_" . showsPrec prec (unUnique uni)) strstr mhint
    showsPrec prec (LV_Named name) = strstr name

noLamType :: LamType
noLamType = LamType Nothing

mkLamType :: MonoType Int -> LamType
mkLamType = LamType . Just

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
mkNIdx i
    | i >= 0 = NIdx i
    | otherwise = undefined

{-# INLINABLE mkNApp #-}
mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (NCon (DC (DC_Succ)) _) (NCon (DC (DC_NatL n)) _) = n' `seq` mkNCon (DC_NatL n') where
    n' = n + 1
mkNApp t1 t2 = NApp t1 t2 Nothing

{-# INLINE mkNAppLoc #-}
mkNAppLoc :: Maybe SLoc -> TermNode -> TermNode -> TermNode
mkNAppLoc sl (NCon (DC (DC_Succ)) _) (NCon (DC (DC_NatL n)) _) = n' `seq` mkNConLoc sl (DC_NatL n') where
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
substTyMTV mtv uni term = assertNonnegativeIndices term `seq` go term where
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
    goMono (TyMTV m) = if m == mtv then refTy else TyMTV m
    goMono (TyApp a b) = TyApp (goMono a) (goMono b)
    goMono t = t

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
    dispatch (NApp t1 t2 sl)
        | NLam _ _ t11 _ <- t1' = beta t11
        | option == WHNF = mkNAppLoc sl t1' (mkSusp t2 ol nl env)
        | option == HNF = mkNAppLoc sl (rewriteWithSuspUnchecked t1' 0 0 [] option) (mkSusp t2 ol nl env)
        | option == NF = mkNAppLoc sl (rewriteWithSuspUnchecked t1' 0 0 [] option) (rewriteWithSuspUnchecked t2 ol nl env option)
        where
            t1' :: TermNode
            t1' = rewriteWithSuspUnchecked t1 ol nl env WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' ol' nl' (Dummy l' : env'))
                | nl' == l' = rewriteWithSuspUnchecked t' ol' (pred nl') (mkBinds (mkSusp t2 ol nl env) (pred l') : env') option
            beta t' = rewriteWithSuspUnchecked t' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
    dispatch (NLam h ty t1 sl)
        | option == WHNF = mkNLamLoc sl h ty (mkSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
        | otherwise = mkNLamLoc sl h ty (rewriteWithSuspUnchecked t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option)
    dispatch (Susp t' ol' nl' env')
        | ol' == 0 && nl' == 0 = rewriteWithSuspUnchecked t' ol nl env option
        | ol == 0 = rewriteWithSuspUnchecked t' ol' (nl + nl') env' option
        | otherwise = rewriteWithSuspUnchecked (rewriteWithSuspUnchecked t' ol' nl' env' WHNF) ol nl env option
    dispatch (NPresburgerCheck rep freeOf sl)
        = NPresburgerCheck rep (Map.map (\t' -> rewriteWithSuspUnchecked t' ol nl env option) freeOf) sl

{-# INLINE rewrite #-}
rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = assertNonnegativeIndices t `seq` case t of
    LVar {} -> t
    NCon {} -> t
    NIdx i
        | i >= 0 -> t
        | otherwise -> undefined
    NPresburgerCheck rep freeOf sl -> NPresburgerCheck rep (Map.map (rewrite option) freeOf) sl
    _ -> rewriteWithSuspUnchecked t 0 0 [] option

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp term = assertNonnegativeIndices term `seq` go term [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go t@(NCon (DC (DC_NatL n)) _) ts
        | n == 0 = (mkNCon (DC_NatL 0), ts)
        | n > 0 = n' `seq` (mkNCon DC_Succ, mkNCon (DC_NatL n') : ts)
        | otherwise = (t, ts)
        where
            n' = n - 1
    go (NApp t1 t2 _) ts
        = go t1 (t2 : ts)
    go t ts
        = (t, ts)

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
    | h `elem` live = pickFresh
    | otherwise = h
    where
        isDigitChar c = c >= '0' && c <= '9'
        rev_rest = dropWhile isDigitChar (reverse h)
        base = if null rev_rest then h else reverse rev_rest
        pickFresh = go (1 :: Int)
        go i = if cand `elem` live then go (i + 1) else cand where
            cand = base ++ show i

viewNestedNLam :: TermNode -> (Int, TermNode)
viewNestedNLam term = assertNonnegativeIndices term `seq` go 0 term where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NLam _ _ t _) = go (n + 1) t
    go n t = (n, t)

viewNestedNLamH :: TermNode -> ([Maybe SmallId], TermNode)
viewNestedNLamH term = assertNonnegativeIndices term `seq` go [] term where
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
defaultCheckOper "+" = Just (InfixL () " + " (), 6)
defaultCheckOper "-" = Just (InfixL () " - " (), 6)
defaultCheckOper "*" = Just (InfixL () " * " (), 7)
defaultCheckOper "/" = Just (InfixL () " / " (), 7)
defaultCheckOper _ = Nothing

constructViewerCustom :: (String -> Maybe (Fixity (), Precedence)) -> (LogicVar -> Maybe SmallId) -> TermNode -> ViewNode
constructViewerCustom checkOper lookupName term = fst . runIdentity $ runStateT (formatView rendered_names (eraseType raw_view)) next_fresh where
    normalized :: TermNode
    normalized = rewrite NF term
    raw_view :: ViewNode
    next_fresh :: Int
    (raw_view, next_fresh) = runIdentity (runStateT (makeView [] normalized) 1)
    free_names :: Set.Set SmallId
    free_names = collectFreeNames normalized
    rendered_names :: Set.Set SmallId
    rendered_names = collectViewNames raw_view
    displayLogicName :: LogicVar -> SmallId
    displayLogicName var = case lookupName var of
        Just cached -> cached
        Nothing -> case var of
            LV_ty_var v -> "?TV_" ++ show v
            LV_Unique v (DispHint mhint) -> case mhint of
                Just hint -> hint
                Nothing -> "?V_" ++ show v
            LV_Named name -> name
    collectFreeNames :: TermNode -> Set.Set SmallId
    collectFreeNames (LVar var) = case var of
        LV_ty_var _ -> Set.empty
        _ -> Set.singleton (displayLogicName var)
    collectFreeNames (NCon con _) = case con of
        DC (DC_Named name) -> Set.singleton name
        DC (DC_Unique uni (DispHint mhint)) -> Set.singleton (case mhint of
            Just hint -> hint
            Nothing -> "c_" ++ show uni)
        _ -> Set.empty
    collectFreeNames (NIdx i)
        | i >= 0 = Set.empty
        | otherwise = undefined
    collectFreeNames (NApp t1 t2 _) = Set.union (collectFreeNames t1) (collectFreeNames t2)
    collectFreeNames (NLam _ _ t _) = collectFreeNames t
    collectFreeNames (Susp body _ _ env) = Set.unions (collectFreeNames body : map collectItemNames env) where
        collectItemNames (Dummy _) = Set.empty
        collectItemNames (Binds t _) = collectFreeNames t
    collectFreeNames (NPresburgerCheck _ freeOf _) = Set.unions (map collectFreeNames (Map.elems freeOf))
    collectViewNames :: ViewNode -> Set.Set SmallId
    collectViewNames viewer = case viewer of
        ViewIVar var -> Set.singleton var
        ViewLVar var -> Set.singleton var
        ViewDCon ('_' : '_' : con) -> Set.singleton con
        ViewDCon con -> Set.singleton con
        ViewIApp t1 t2 -> Set.union (collectViewNames t1) (collectViewNames t2)
        ViewIAbs var t -> Set.insert var (collectViewNames t)
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
    freshGeneratedName :: Set.Set SmallId -> StateT Int Identity SmallId
    freshGeneratedName forbidden = do
        candidate0 <- get
        let name candidate = "W_" ++ show candidate
            pick candidate
                | Set.member (name candidate) forbidden = pick (candidate + 1)
                | otherwise = candidate
            candidate = pick candidate0
        put (candidate + 1)
        return (name candidate)
    isType :: ViewNode -> Bool
    isType (ViewTVar _) = True
    isType (ViewTCon _) = True
    isType (ViewTApp _ _) = True
    isType _ = False
    makeView :: [SmallId] -> TermNode -> StateT Int Identity ViewNode
    makeView vars (LVar var) = case var of
        LV_ty_var v -> return (ViewTVar ("?TV_" ++ show v))
        LV_Unique {} -> return (ViewLVar (displayLogicName var))
        LV_Named {} -> return (ViewLVar (displayLogicName var))
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
    makeView vars (NIdx idx)
        | idx < 0 = undefined
        | var : _ <- drop idx vars = return (ViewIVar var)
        | otherwise = undefined
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
            chosen = freshenName preferred (vars ++ Set.toList free_names)
        t_rep <- makeView (chosen : vars) t
        return (ViewIAbs chosen t_rep)
    makeView vars (NPresburgerCheck rep freeOf _) = do
        rendered <- renderPresburger vars rep freeOf
        return (ViewDCon rendered)
    makeView vars (Susp body _ _ _) = makeView vars body

    renderPresburger :: [SmallId] -> MyPresburgerFormulaRep -> Map.Map MyVar TermNode -> StateT Int Identity SmallId
    renderPresburger vars rep freeOf = do
        body <- renderFormula 0 Map.empty rep
        return ("presburger \"" ++ body ++ "\"")
        where
            parensText :: Bool -> String -> String
            parensText True s = "(" ++ s ++ ")"
            parensText False s = s

            varName :: MyVar -> SmallId
            varName v = showsMyVar v ""

            renderFormula :: Precedence -> Map.Map MyVar SmallId -> MyPresburgerFormulaRep -> StateT Int Identity SmallId
            renderFormula prec bound formula =
                case formula of
                    ValF b ->
                        return (parensText (prec > 4) (if b then "~ _|_" else "_|_"))
                    EqnF t1 t2 ->
                        renderRelation "=" t1 t2
                    LtnF t1 t2 ->
                        renderRelation "<" t1 t2
                    LeqF t1 t2 ->
                        renderRelation "=<" t1 t2
                    GtnF t1 t2 ->
                        renderRelation ">" t1 t2
                    ModF t1 r t2 ->
                        renderRelation ("==_{" ++ show r ++ "}") t1 t2
                    NegF f1 -> do
                        s1 <- renderFormula 4 bound f1
                        return (parensText (prec > 3) ("~ " ++ s1))
                    DisF f1 f2 -> do
                        s1 <- renderFormula 1 bound f1
                        s2 <- renderFormula 2 bound f2
                        return (parensText (prec > 1) (s1 ++ " \\/ " ++ s2))
                    ConF f1 f2 -> do
                        s1 <- renderFormula 3 bound f1
                        s2 <- renderFormula 2 bound f2
                        return (parensText (prec > 2) (s1 ++ " /\\ " ++ s2))
                    ImpF f1 f2 -> do
                        s1 <- renderFormula 1 bound f1
                        s2 <- renderFormula 0 bound f2
                        return (parensText (prec > 0) (s1 ++ " -> " ++ s2))
                    IffF f1 f2 -> do
                        s1 <- renderFormula 1 bound f1
                        s2 <- renderFormula 1 bound f2
                        return (parensText (prec > 0) (s1 ++ " <-> " ++ s2))
                    AllF y f1 ->
                        renderQuantifier "forall" y f1
                    ExsF y f1 ->
                        renderQuantifier "exists" y f1
                where
                    renderRelation oper t1 t2 = do
                        s1 <- renderTerm 0 bound t1
                        s2 <- renderTerm 0 bound t2
                        return (parensText (prec > 4) (s1 ++ " " ++ oper ++ " " ++ s2))
                    renderQuantifier kw y f1 = do
                        let yName = varName y
                        s1 <- renderFormula 3 (Map.insert y yName bound) f1
                        return (parensText (prec > 3) (kw ++ " " ++ yName ++ ", " ++ s1))

            renderTerm :: Precedence -> Map.Map MyVar SmallId -> PresburgerTermRep -> StateT Int Identity SmallId
            renderTerm prec bound term =
                case foldedNat term of
                    Just n ->
                        return (show n)
                    Nothing ->
                        case term of
                            IVar v ->
                                case Map.lookup v bound of
                                    Just name -> return name
                                    Nothing -> case Map.lookup v freeOf of
                                        Just t -> renderFreeTerm vars t
                                        Nothing -> return (varName v)
                            Zero ->
                                return "O"
                            Succ t1 -> do
                                s1 <- renderTerm 2 bound t1
                                return (parensText (prec > 1) ("S " ++ s1))
                            Plus t1 t2 -> do
                                s1 <- renderTerm 0 bound t1
                                s2 <- renderTerm 1 bound t2
                                return (parensText (prec > 0) (s1 ++ " + " ++ s2))

            renderFreeTerm :: [SmallId] -> TermNode -> StateT Int Identity SmallId
            renderFreeTerm boundVars t = do
                v <- makeView boundVars (rewrite NF t)
                v' <- formatView (collectViewNames v) (eraseType v)
                return (pprint 0 v' "")

            foldedNat :: PresburgerTermRep -> Maybe Integer
            foldedNat Zero = Just 0
            foldedNat (Succ t1) = succ <$> foldedNat t1
            foldedNat (Plus t1 t2) = (+) <$> foldedNat t1 <*> foldedNat t2
            foldedNat (IVar _) = Nothing
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
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n2 (ViewOper (InfixL t1' str (ViewIVar n2), prec)))
            InfixR _ str _ -> do
                t1' <- formatView forbidden t1
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n2 (ViewOper (InfixR t1' str (ViewIVar n2), prec)))
            InfixN _ str _ -> do
                t1' <- formatView forbidden t1
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n2 (ViewOper (InfixN t1' str (ViewIVar n2), prec)))
    formatView forbidden (ViewDCon con)
        | Just (oper, prec) <- checkOper con
        = case oper of
            Prefix str _ -> do
                n1 <- freshGeneratedName forbidden
                return (ViewIAbs n1 (ViewOper (Prefix str (ViewIVar n1), prec)))
            InfixL _ str _ -> do
                n1 <- freshGeneratedName forbidden
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n1 (ViewIAbs n2 (ViewOper (InfixL (ViewIVar n1) str (ViewIVar n2), prec))))
            InfixR _ str _ -> do
                n1 <- freshGeneratedName forbidden
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n1 (ViewIAbs n2 (ViewOper (InfixR (ViewIVar n1) str (ViewIVar n2), prec))))
            InfixN _ str _ -> do
                n1 <- freshGeneratedName forbidden
                n2 <- freshGeneratedName forbidden
                return (ViewIAbs n1 (ViewIAbs n2 (ViewOper (InfixN (ViewIVar n1) str (ViewIVar n2), prec))))
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
