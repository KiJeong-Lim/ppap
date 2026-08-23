
module Hol.ALPHA2.TypeChecker where

import Hol.ALPHA2.Constant
import Hol.ALPHA2.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

infix 4 +->
infix 4 ->>

data TypeError
    = KindsAreMismatched (MonoType Int, KindExpr) (MonoType Int, KindExpr)
    | OccursCheckFailed MetaTVar (MonoType Int)
    | TypesAreMismatched (MonoType Int) (MonoType Int)
    | MalformedTypeApplication (MonoType Int)
    deriving ()

newtype TypeSubst
    = TypeSubst { getTypeSubst :: Map.Map MetaTVar (MonoType Int) }
    deriving ()

-- Retain the source occurrences which contributed each logic-variable type.
-- The public inference API still exposes the historic map from variables to
-- types; this richer form exists only long enough to produce useful errors.
data TypeAssumption
    = TypeAssumption
        { assumptionType :: !(MonoType Int)
        , assumptionLocs :: ![SLoc]
        }

data ApplicationConstraintOrigin
    = FunctionApplicationConstraint
    | SharedVariableConstraint !IVar !SLoc !SLoc

class HasMTVar a where
    getFreeMTVs :: a -> Set.Set MetaTVar -> Set.Set MetaTVar
    substMTVars :: TypeSubst -> a -> a

instance IsInt tvar => HasMTVar (MonoType tvar) where
    getFreeMTVs (TyMTV mtv) = Set.insert mtv
    getFreeMTVs (TyVar tvar) = id
    getFreeMTVs (TyCon tcon) = id
    getFreeMTVs (TyApp typ1 typ2) = getFreeMTVs typ1 . getFreeMTVs typ2
    substMTVars (TypeSubst { getTypeSubst = mapsto }) = go where
        convert :: IsInt tvar => MonoType Int -> MonoType tvar
        convert (TyVar tvar) = TyVar (fromInt tvar)
        convert (TyCon tcon) = TyCon tcon
        convert (TyApp typ1 typ2) = TyApp (convert typ1) (convert typ2)
        convert (TyMTV mtv) = TyMTV mtv
        go :: IsInt tvar => MonoType tvar -> MonoType tvar
        go typ = case typ of
            TyMTV mtv -> maybe typ convert (Map.lookup mtv mapsto)
            TyApp typ1 typ2 -> TyApp (go typ1) (go typ2)
            TyVar tvar -> TyVar tvar
            TyCon tcon -> TyCon tcon

instance HasMTVar a => HasMTVar [a] where
    getFreeMTVs = flip (foldr getFreeMTVs)
    substMTVars = map . substMTVars

instance HasMTVar b => HasMTVar (a, b) where
    getFreeMTVs = snd . fmap getFreeMTVs
    substMTVars = fmap . substMTVars

instance HasMTVar a => HasMTVar (Map.Map k a) where
    getFreeMTVs = getFreeMTVs . Map.elems
    substMTVars = Map.map . substMTVars

instance HasMTVar TypeAssumption where
    getFreeMTVs = getFreeMTVs . assumptionType
    substMTVars theta assumption = assumption
        { assumptionType = substMTVars theta (assumptionType assumption) }

instance Semigroup TypeSubst where
    theta2 <> theta1 = TypeSubst { getTypeSubst = Map.map (substMTVars theta2) (getTypeSubst theta1) `Map.union` (getTypeSubst theta2) }

instance Monoid TypeSubst where
    mempty = TypeSubst { getTypeSubst = Map.empty }

(+->) :: MetaTVar -> MonoType Int -> Either TypeError TypeSubst
mtv +-> typ 
    | TyMTV mtv == typ = return mempty
    | mtv `Set.member` getFMTVs typ = Left (OccursCheckFailed mtv typ)
    | otherwise = case (getKindEither (TyMTV mtv), getKindEither typ) of
        (Right mtvKind, Right typKind)
            | mtvKind == typKind -> return (TypeSubst (Map.singleton mtv typ))
            | otherwise -> Left (KindsAreMismatched (TyMTV mtv, mtvKind) (typ, typKind))
        (Left typError, _) -> Left typError
        (_, Left typError) -> Left typError

getFMTVs :: HasMTVar a => a -> Set.Set MetaTVar
getFMTVs = flip getFreeMTVs Set.empty

getKind :: MonoType Int -> KindExpr
getKind = either (const undefined) id . getKindEither

getKindEither :: MonoType Int -> Either TypeError KindExpr
getKindEither typ = case typ of
    TyVar _ -> return Star
    TyCon (TCon _ kin) -> return kin
    TyApp typ1 typ2 -> case (getKindEither typ1, getKindEither typ2) of
        (Right (argumentKind `KArr` resultKind), Right actualArgumentKind)
            | argumentKind == actualArgumentKind -> return resultKind
            | otherwise -> Left (MalformedTypeApplication typ)
        (Right _, Right _) -> Left (MalformedTypeApplication typ)
        (Left typError, _) -> Left typError
        (_, Left typError) -> Left typError
    TyMTV _ -> return Star

getMGU :: Monad mnd => MonoType Int -> MonoType Int -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
getMGU lhs rhs
    = case validateKinds lhs rhs of
        Left typ_error -> throwE ((lhs, rhs), typ_error)
        Right () -> case go Set.empty lhs rhs of
            (Nothing, theta) -> return theta
            (Just typ_error, theta) -> throwE ((substMTVars theta lhs, substMTVars theta rhs), typ_error)
    where
        go :: Set.Set MetaTVar -> MonoType Int -> MonoType Int -> (Maybe TypeError, TypeSubst)
        go _ (TyVar tvar1) (TyVar tvar2)
            | tvar1 == tvar2 = (Nothing, mempty)
        go _ typ1@(TyVar _) typ2 = (Just (TypesAreMismatched typ1 typ2), mempty)
        go _ typ1 typ2@(TyVar _) = (Just (TypesAreMismatched typ1 typ2), mempty)
        go _ typ1@(TyCon tcon1) typ2@(TyCon tcon2)
            | typesAgreeIncludingKinds typ1 typ2 = (Nothing, mempty)
            | tcon1 == tcon2 = (Just (KindsAreMismatched (typ1, getTConKind tcon1) (typ2, getTConKind tcon2)), mempty)
        go lockeds (TyMTV mtv) typ 
            | mtv `Set.member` lockeds
            = (Nothing, mempty)
            | otherwise
            = case mtv +-> typ of
                Left typ_error -> (Just typ_error, mempty)
                Right theta -> (Nothing, theta)
        go lockeds typ (TyMTV mtv)
            | mtv `Set.member` lockeds
            = (Nothing, mempty)
            | otherwise
            = case mtv +-> typ of
                Left typ_error -> (Just typ_error, mempty)
                Right theta -> (Nothing, theta)
        go lockeds (TyApp typ1 typ2) (TyApp typ1' typ2') = case go lockeds typ1 typ1' of
            (Nothing, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Nothing, theta2 <> theta1)
                (Just typ_error, theta2) -> (Just typ_error, theta2 <> theta1)
            (Just (OccursCheckFailed mtv typ), theta1) -> case go (Set.insert mtv lockeds) (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Just (OccursCheckFailed mtv typ), theta2 <> theta1)
                (Just typ_error', theta2) -> (Just typ_error', theta2 <> theta1)
            (Just typ_error, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                (Nothing, theta2) -> (Just typ_error, theta2 <> theta1)
                (Just typ_error', theta2) -> (Just typ_error, theta2 <> theta1)
        go lockeds typ1 typ2 = (Just (TypesAreMismatched typ1 typ2), mempty)

unify :: Monad mnd => [(MonoType Int, MonoType Int)] -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
unify [] = return mempty
unify ((lhs, rhs) : disgrees) = do
    theta1 <- getMGU lhs rhs
    theta2 <- unify [ (substMTVars theta1 lhs0, substMTVars theta1 rhs0) | (lhs0, rhs0) <- disgrees ]
    return (theta2 <> theta1)

-- As 'unify', but retain both the complete constraint and the source reason
-- for it.  'getMGU' may report only an inner component of a failed equation,
-- while a source diagnostic needs the types required by both occurrences.
unifyWithProvenance :: Monad mnd => [(origin, MonoType Int, MonoType Int)] -> ExceptT (origin, MonoType Int, MonoType Int, ((MonoType Int, MonoType Int), TypeError)) mnd TypeSubst
unifyWithProvenance [] = return mempty
unifyWithProvenance ((origin, lhs, rhs) : constraints) = do
    theta1 <- withExceptT (\mismatch -> (origin, lhs, rhs, mismatch)) (getMGU lhs rhs)
    theta2 <- unifyWithProvenance
        [ (constraintOrigin, substMTVars theta1 constraintLhs, substMTVars theta1 constraintRhs)
        | (constraintOrigin, constraintLhs, constraintRhs) <- constraints
        ]
    return (theta2 <> theta1)

(->>) :: Monad mnd => MonoType Int -> MonoType Int -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
lhs ->> rhs
    = case validateKinds lhs rhs of
        Left typ_error -> throwE ((lhs, rhs), typ_error)
        Right () -> case go lhs rhs of
            Right theta -> return theta
            Left typ_error -> throwE ((lhs, rhs), typ_error)
    where
        merge :: TypeSubst -> TypeSubst -> Either (MonoType Int, MonoType Int) TypeSubst
        merge (TypeSubst mapsto1) (TypeSubst mapsto2)
            = case disgrees of
                [] -> Right (TypeSubst mapsto2 <> TypeSubst mapsto1)
                (typ1, typ2) : _ -> Left (typ1, typ2)
            where
                disgrees :: [(MonoType Int, MonoType Int)]
                disgrees = do
                    mtv <- Set.toList (Map.keysSet mapsto1 `Set.intersection` Map.keysSet mapsto2)
                    let typ1 = mapsto1 Map.! mtv
                        typ2 = mapsto2 Map.! mtv
                    if typesAgreeIncludingKinds typ1 typ2
                        then []
                        else return (typ1, typ2)
        go :: MonoType Int -> MonoType Int -> Either TypeError TypeSubst
        go (TyVar tvar1) (TyVar tvar2)
            | tvar1 == tvar2 = return mempty
        go typ1@(TyVar _) typ2 = Left (TypesAreMismatched typ1 typ2)
        go typ1 typ2@(TyVar _) = Left (TypesAreMismatched typ1 typ2)
        go typ1@(TyCon tcon1) typ2@(TyCon tcon2)
            | typesAgreeIncludingKinds typ1 typ2 = return mempty
            | tcon1 == tcon2 = Left (KindsAreMismatched (typ1, getTConKind tcon1) (typ2, getTConKind tcon2))
        go (TyMTV mtv) typ
            = mtv +-> typ
        go (TyApp typ1 typ2) (TyApp typ1' typ2') = do
            theta1 <- go typ1 typ1'
            theta2 <- go typ2 typ2'
            case merge theta1 theta2 of
                Left (typ, typ') -> Left (TypesAreMismatched typ typ')
                Right theta -> return theta
        go typ1 typ2 = Left (TypesAreMismatched typ1 typ2)

validateKinds :: MonoType Int -> MonoType Int -> Either TypeError ()
validateKinds lhs rhs = case (getKindEither lhs, getKindEither rhs) of
    (Left typError, _) -> Left typError
    (_, Left typError) -> Left typError
    (Right lhsKind, Right rhsKind)
        | lhsKind == rhsKind -> Right ()
        | otherwise -> Left (KindsAreMismatched (lhs, lhsKind) (rhs, rhsKind))

getTConKind :: TCon -> KindExpr
getTConKind (TCon _ kindExpr) = kindExpr

typesAgreeIncludingKinds :: MonoType Int -> MonoType Int -> Bool
typesAgreeIncludingKinds lhs rhs = case (lhs, rhs) of
    (TyVar v1, TyVar v2) -> v1 == v2
    (TyMTV v1, TyMTV v2) -> v1 == v2
    (TyCon (TCon c1 k1), TyCon (TCon c2 k2)) -> c1 == c2 && k1 == k2
    (TyApp f1 x1, TyApp f2 x2) ->
        typesAgreeIncludingKinds f1 f2 && typesAgreeIncludingKinds x1 x2
    _ -> False

showMonoType :: Map.Map MetaTVar LargeId -> MonoType Int -> String -> String
showMonoType name_env = go 0 where
    go :: Precedence -> MonoType Int -> String -> String
    go prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2)
        | prec <= 0 = go 1 typ1 . strstr " -> " . go 0 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " -> " . go 0 typ2 . strstr ")"
    go prec (TyApp typ1 typ2)
        | prec <= 1 = go 1 typ1 . strstr " " . go 2 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " " . go 2 typ2 . strstr ")"
    go prec (TyCon con)
        = pprint 0 con
    go prec (TyVar var)
        = strstr "#" . showsPrec 0 var
    go prec (TyMTV mtv)
        = case Map.lookup mtv name_env of
            Nothing -> strstr "mtv_" . showsPrec 0 mtv
            Just name -> strstr name

instantiateScheme :: MonadUnique m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateScheme = instantiateSchemeUsing malformed where
    malformed idx count = typeErrorNoLoc
        [ "Malformed polymorphic type declaration."
        , "Type-variable index #" ++ show idx ++ " is outside a forall with "
            ++ show count ++ " binder(s)."
        ]

instantiateSchemeAt :: MonadUnique m => SLoc -> PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateSchemeAt loc = instantiateSchemeUsing malformed where
    malformed idx count = typeErrorAt loc
        [ "Malformed polymorphic type declaration."
        , "Type-variable index #" ++ show idx ++ " is outside a forall with "
            ++ show count ++ " binder(s)."
        , "Check the declaration's quantified type variables."
        ]

instantiateSchemeUsing
    :: MonadUnique m
    => (Int -> Int -> ErrMsg)
    -> PolyType
    -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateSchemeUsing malformed (Forall tvars typ) = do
    mtvs <- mapM getNewMTV tvars
    case instantiateBody (map TyMTV mtvs) typ of
        Left idx -> lift (throwE (malformed idx (length tvars)))
        Right instantiated -> return (mtvs, instantiated)
  where
    instantiateBody :: [MonoType Int] -> MonoType Int -> Either Int (MonoType Int)
    instantiateBody replacements mono = case mono of
        TyVar idx
            | idx < 0 -> Left idx
            | otherwise -> maybe (Left idx) Right (atMay replacements idx)
        TyCon tcon -> return (TyCon tcon)
        TyApp typ1 typ2 -> TyApp <$> instantiateBody replacements typ1
            <*> instantiateBody replacements typ2
        TyMTV mtv -> return (TyMTV mtv)
    atMay :: [a] -> Int -> Maybe a
    atMay [] _ = Nothing
    atMay (x : _) 0 = Just x
    atMay (_ : xs) n = atMay xs (n - 1)

getNewMTV :: MonadUnique m => LargeId -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) MetaTVar
getNewMTV largeid
    = do
        used_mtvs_0 <- get
        mtv <- getUnique
        let name = makeName used_mtvs_0 largeid
        put (Map.insert mtv name used_mtvs_0)
        return mtv
    where
        makeName :: Map.Map MetaTVar LargeId -> LargeId -> LargeId
        makeName used_mtvs smallid = go 0 where
            go :: Int -> LargeId
            go n = if name `elem` Map.elems used_mtvs then go (n + 1) else name where
                name :: String
                name = smallid ++ "_" ++ show n

zonkMTV :: TypeSubst -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
zonkMTV theta = go where
    go :: TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
    go (Var (loc, typ) var) = Var (loc, substMTVars theta typ) var
    go (Con (loc, typ) (con, tapps)) = Con (loc, substMTVars theta typ) (con, substMTVars theta tapps)
    go (App (loc, typ) term1 term2) = App (loc, substMTVars theta typ) (go term1) (go term2)
    go (Lam (loc, typ) var term) = Lam (loc, substMTVars theta typ) var (go term)

typeErrorAt :: SLoc -> [String] -> ErrMsg
typeErrorAt loc details = concat
    [ "*** typechecking-error[", pprint 0 loc "]:\n"
    , concatMap (\detail -> "  " ++ detail ++ "\n") details
    ]

typeErrorNoLoc :: [String] -> ErrMsg
typeErrorNoLoc details = concat
    [ "*** typechecking-error:\n"
    , concatMap (\detail -> "  " ++ detail ++ "\n") details
    ]

showType :: Map.Map MetaTVar LargeId -> MonoType Int -> String
showType usedMTVs typ = showMonoType usedMTVs typ ""

typeErrorReason :: Map.Map MetaTVar LargeId -> TypeError -> String
typeErrorReason usedMTVs typError = case typError of
    KindsAreMismatched (_, kind1) (_, kind2) ->
        "kind mismatch: `" ++ pprint 0 kind1 "' vs `" ++ pprint 0 kind2 "'."
    OccursCheckFailed mtv typ ->
        "occurs check failed; `" ++ ty (TyMTV mtv)
            ++ "' would contain `" ++ ty typ ++ "'."
    TypesAreMismatched typ1 typ2 ->
        "`" ++ ty typ1 ++ "' is not unifiable with `" ++ ty typ2 ++ "'."
    MalformedTypeApplication typ ->
        "malformed type application `" ++ ty typ ++ "'."
  where
    ty = showType usedMTVs

mkTyErr :: Map.Map MetaTVar LargeId -> SLoc -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkTyErr usedMTVs loc ((actualType, expectedType), typError) = typeErrorAt loc
    [ "Context: type mismatch while checking a function application."
    , "Expected: `" ++ ty expectedType ++ "'"
    , "Actual:   `" ++ ty actualType ++ "'"
    , "Reason: " ++ typeErrorReason usedMTVs typError
    ]
  where
    ty = showType usedMTVs

mkApplicationTyErr
    :: Map.Map MetaTVar LargeId
    -> SLoc
    -> SLoc
    -> SLoc
    -> Bool
    -> MonoType Int
    -> MonoType Int
    -> MonoType Int
    -> ((MonoType Int, MonoType Int), TypeError)
    -> ErrMsg
mkApplicationTyErr usedMTVs appLoc functionLoc argumentLoc isSelf
        actualFunction actualArgument resultType mismatch@(_, typError)
    | isSelf && isOccursFailure typError = typeErrorAt appLoc
        [ "Self-application requires an infinite type."
        , "Actual:   `" ++ ty selfActual ++ "'"
        , "Required: `" ++ ty selfRequired ++ "'"
        , "A value cannot be applied to itself in this simply typed language."
        ]
    | not (isFunctionType actualFunction) && not (isMetaType actualFunction) =
        typeErrorAt functionLoc
            [ "Cannot apply a non-function value."
            , "Actual:   `" ++ ty actualFunction ++ "'"
            , "Expected: `" ++ ty requiredFunction ++ "'"
            , "The expression in function position must have a function type."
            ]
    | Just (expectedArgument, _) <- viewArrow actualFunction
    , typesDefinitelyDisagree expectedArgument actualArgument =
        typeErrorAt argumentLoc
            [ "Function argument has the wrong type."
            , "Expected: `" ++ ty expectedArgument ++ "'"
            , "Actual:   `" ++ ty actualArgument ++ "'"
            ]
    | otherwise = mkTyErr usedMTVs argumentLoc mismatch
  where
    ty = showType usedMTVs
    requiredFunction = actualArgument `mkTyArrow` resultType
    viewArrow (TyApp (TyApp (TyCon (TCon TC_Arrow _)) domain) codomain) =
        Just (domain, codomain)
    viewArrow _ = Nothing
    isFunctionType = maybe False (const True) . viewArrow
    isMetaType (TyMTV _) = True
    isMetaType _ = False
    isOccursFailure (OccursCheckFailed _ _) = True
    isOccursFailure _ = False
    (selfActual, selfRequired) = case typError of
        OccursCheckFailed mtv typ -> (TyMTV mtv, typ)
        _ -> (actualFunction, requiredFunction)
    typesDefinitelyDisagree (TyMTV _) _ = False
    typesDefinitelyDisagree _ (TyMTV _) = False
    typesDefinitelyDisagree (TyVar _) _ = False
    typesDefinitelyDisagree _ (TyVar _) = False
    typesDefinitelyDisagree typ1@(TyCon _) typ2@(TyCon _) =
        not (typesAgreeIncludingKinds typ1 typ2)
    typesDefinitelyDisagree (TyApp function1 argument1) (TyApp function2 argument2) =
        typesDefinitelyDisagree function1 function2
            || typesDefinitelyDisagree argument1 argument2
    typesDefinitelyDisagree (TyApp _ _) (TyCon _) = True
    typesDefinitelyDisagree (TyCon _) (TyApp _ _) = True

mkSharedVariableTyErr
    :: Map.Map MetaTVar LargeId
    -> SLoc
    -> SLoc
    -> MonoType Int
    -> MonoType Int
    -> ErrMsg
mkSharedVariableTyErr usedMTVs earlierLoc conflictingLoc
        earlierType conflictingType = typeErrorAt conflictingLoc
    [ "The same logic variable has conflicting type requirements."
    , "Earlier occurrence at " ++ pprint 0 earlierLoc " requires:     `"
        ++ ty earlierType ++ "'"
    , "Conflicting occurrence at " ++ pprint 0 conflictingLoc " requires: `"
        ++ ty conflictingType ++ "'"
    , "Every occurrence of a logic variable in one expression must have the same type."
    ]
  where
    ty = showType usedMTVs

mkExpectedTyErr
    :: Map.Map MetaTVar LargeId
    -> SLoc
    -> MonoType Int
    -> MonoType Int
    -> ((MonoType Int, MonoType Int), TypeError)
    -> ErrMsg
mkExpectedTyErr usedMTVs loc actualType expectedType (_, typError) =
    typeErrorAt loc
        ( [ "Expression has the wrong result type."
          , "Expected: `" ++ ty expectedType ++ "'"
          , "Actual:   `" ++ ty actualType ++ "'"
          ]
          ++ goalHint
          ++ reasonLine typError
        )
  where
    ty = showType usedMTVs
    goalHint
        | expectedType == mkTyO =
            [ "Hint: a query or fact must have proposition type `o'."
            , "      Apply a predicate or add a comparison if a proposition was intended."
            ]
        | otherwise = []
    reasonLine (TypesAreMismatched _ _) = []
    reasonLine reason = ["Reason: " ++ typeErrorReason usedMTVs reason]

mkUnknownConErr :: SLoc -> DataConstructor -> ErrMsg
mkUnknownConErr loc con = typeErrorAt loc
    [ "Unknown predicate or constructor `" ++ showsPrec 0 con "'."
    , "No type declaration for this name is visible here."
    , "Declare it with `type', import its module, or check the spelling."
    ]

inferType :: MonadUnique m => TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferType typeEnv term = do
    ((inferredTerm, assumptions), usedMTVs) <- runStateT (infer term) Map.empty
    return ((inferredTerm, Map.map assumptionType assumptions), usedMTVs)
  where
    infer :: MonadUnique m => TermExpr DataConstructor SLoc -> StateT (Map.Map MetaTVar SmallId) (ExceptT ErrMsg m) (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar TypeAssumption)
    infer (Var loc var) = do
        mtv <- getNewMTV "A"
        return (Var (loc, TyMTV mtv) var,
            Map.singleton var (TypeAssumption (TyMTV mtv) [loc]))
    infer (Con loc con) = case con of
        DC_ChrL _ -> return (Con (loc, mkTyChr) (con, []), Map.empty)
        DC_NatL _ -> return (Con (loc, mkTyNat) (con, []), Map.empty)
        DC_wc -> do
            var <- getUnique
            mtv <- getNewMTV "A"
            return (Con (loc, TyMTV mtv) (con, []),
                Map.singleton var (TypeAssumption (TyMTV mtv) [loc]))
        _ -> do
            (mtvs, typ) <- case Map.lookup con typeEnv of
                Nothing -> lift (throwE (mkUnknownConErr loc con))
                Just scheme -> instantiateSchemeAt loc scheme
            return (Con (loc, typ) (con, map TyMTV mtvs), Map.empty)
    infer (App loc term1 term2) = do
        (term1', assumptions1) <- infer term1
        (term2', assumptions2) <- infer term2
        mtv <- getNewMTV "A"
        usedMTVs <- get
        let sharedVariables = Set.toList
                (Map.keysSet assumptions1 `Set.intersection` Map.keysSet assumptions2)
            constraints =
                ( FunctionApplicationConstraint
                , snd (getAnnot term1')
                , snd (getAnnot term2') `mkTyArrow` TyMTV mtv
                ) : map sharedVariableConstraint sharedVariables
            sharedVariableConstraint variable =
                let earlierAssumption = assumptions1 Map.! variable
                    conflictingAssumption = assumptions2 Map.! variable
                in ( SharedVariableConstraint variable
                        (firstAssumptionLoc (fst (getAnnot term1')) earlierAssumption)
                        (firstAssumptionLoc (fst (getAnnot term2')) conflictingAssumption)
                   , assumptionType earlierAssumption
                   , assumptionType conflictingAssumption
                   )
            isSelfApplication = case (term1, term2) of
                (Var _ variable1, Var _ variable2) -> variable1 == variable2
                _ -> False
            applicationError = mkApplicationTyErr usedMTVs loc
                (fst (getAnnot term1')) (fst (getAnnot term2')) isSelfApplication
                (snd (getAnnot term1')) (snd (getAnnot term2')) (TyMTV mtv)
            isOccursFailure (OccursCheckFailed _ _) = True
            isOccursFailure _ = False
        theta <- lift $ catchE (unifyWithProvenance constraints) $
            \(origin, requiredEarlier, requiredHere, mismatch@(_, typError)) ->
                throwE $ case origin of
                    SharedVariableConstraint _ earlierLoc conflictingLoc
                        | not (isSelfApplication && isOccursFailure typError) ->
                            mkSharedVariableTyErr usedMTVs earlierLoc
                                conflictingLoc requiredEarlier requiredHere
                    _ -> applicationError mismatch
        let usedMTVs' = usedMTVs `Map.withoutKeys`
                Map.keysSet (getTypeSubst theta)
            assumptions' = Map.unionWith mergeAssumptions
                (substMTVars theta assumptions1) (substMTVars theta assumptions2)
        put usedMTVs'
        return (zonkMTV theta (App (loc, TyMTV mtv) term1' term2'), assumptions')
    infer (Lam loc var termBody) = do
        (termBody', assumptions) <- infer termBody
        case Map.lookup var assumptions of
            Nothing -> do
                mtv <- getNewMTV "A"
                return ( Lam (loc, TyMTV mtv `mkTyArrow` snd (getAnnot termBody'))
                            var termBody'
                       , assumptions
                       )
            Just assumption -> return
                ( Lam (loc, assumptionType assumption `mkTyArrow` snd (getAnnot termBody'))
                    var termBody'
                , Map.delete var assumptions
                )
    firstAssumptionLoc _ (TypeAssumption _ (loc : _)) = loc
    firstAssumptionLoc fallback (TypeAssumption _ []) = fallback
    mergeAssumptions earlier conflicting = TypeAssumption
        (assumptionType earlier)
        (assumptionLocs earlier ++ assumptionLocs conflicting)

checkType :: MonadUnique m => TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkType typeEnv term expectedType = do
    ((term', assumptions), usedMTVs) <- inferType typeEnv term
    let actualType = snd (getAnnot term')
    theta <- catchE (actualType ->> expectedType) $
        throwE . mkExpectedTyErr usedMTVs (getAnnot term) actualType expectedType
    let usedMTVs' = usedMTVs `Map.withoutKeys` Map.keysSet (getTypeSubst theta)
        assumptions' = substMTVars theta assumptions
    return (zonkMTV theta term', (usedMTVs', assumptions'))
