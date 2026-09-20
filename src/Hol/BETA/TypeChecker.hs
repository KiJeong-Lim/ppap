
module Hol.BETA.TypeChecker where

import Hol.BETA.Constant
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.Notation (NotationDB)
import qualified Hol.BETA.Notation as Notation
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Z.Doc
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

-- Keep the source occurrences that contributed each logic-variable type.  The
-- public checker API still returns the historic map from variables to types;
-- this richer form is only used while inferring a term so a conflict can point
-- back to both uses that imposed incompatible requirements.
data TypeAssumption
    = TypeAssumption
        { assumptionType :: !(MonoType Int)
        , assumptionLocs :: ![SLoc]
        }

data ApplicationConstraintOrigin
    = FunctionApplicationConstraint
    | SharedVariableConstraint !SLoc !SLoc

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

-- 'getKind' keeps its historic pure signature for source compatibility.  Its
-- input domain contains only well-kinded types; use 'getKindEither' at any
-- validation boundary that must report malformed applications structurally.
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
        go _ typ1@(TyVar _) typ2
            = (Just (TypesAreMismatched typ1 typ2), mempty)
        go _ typ1 typ2@(TyVar _)
            = (Just (TypesAreMismatched typ1 typ2), mempty)
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
        go lockeds (TyApp typ1 typ2) (TyApp typ1' typ2')
            = case go lockeds typ1 typ1' of
                (Nothing, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                    (Nothing, theta2) -> (Nothing, theta2 <> theta1)
                    (Just typ_error, theta2) -> (Just typ_error, theta2 <> theta1)
                (Just (OccursCheckFailed mtv typ), theta1) -> case go (Set.insert mtv lockeds) (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                    (Nothing, theta2) -> (Just (OccursCheckFailed mtv typ), theta2 <> theta1)
                    (Just typ_error', theta2) -> (Just typ_error', theta2 <> theta1)
                (Just typ_error, theta1) -> case go lockeds (substMTVars theta1 typ2) (substMTVars theta1 typ2') of
                    (Nothing, theta2) -> (Just typ_error, theta2 <> theta1)
                    (Just typ_error', theta2) -> (Just typ_error, theta2 <> theta1)
        go lockeds typ1 typ2
            = (Just (TypesAreMismatched typ1 typ2), mempty)

unify :: Monad mnd => [(MonoType Int, MonoType Int)] -> ExceptT ((MonoType Int, MonoType Int), TypeError) mnd TypeSubst
unify [] = return mempty
unify ((lhs, rhs) : disgrees) = do
    theta1 <- getMGU lhs rhs
    theta2 <- unify [ (substMTVars theta1 lhs0, substMTVars theta1 rhs0) | (lhs0, rhs0) <- disgrees ]
    return (theta2 <> theta1)

-- As 'unify', but retain the origin and the complete constraint that failed.
-- 'getMGU' may report only a mismatching component (for example the element
-- types of two lists), while a diagnostic should show the full types required
-- by the two source occurrences.
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
                    if typesAgreeIncludingKinds typ1 typ2 then [] else return (typ1, typ2)
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

showMonoType :: NotationDB -> Map.Map MetaTVar LargeId -> MonoType Int -> String -> String
showMonoType db name_env = go 0 where
    go :: Precedence -> MonoType Int -> String -> String
    go prec t = case Notation.tryFoldType db t of
        Just (name, []) -> strstr (renderNamedIdentifier name)
        Just (name, args) -> if prec > 1 then strstr "(" . inner name args . strstr ")" else inner name args
        Nothing -> raw prec t
    inner :: LargeId -> [MonoType Int] -> String -> String
    inner name args = strstr (renderNamedIdentifier name) . List.foldr (.) id [ strstr " " . go 2 a | a <- args ]
    raw :: Precedence -> MonoType Int -> String -> String
    raw prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2)
        | prec <= 0 = go 1 typ1 . strstr " -> " . go 0 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " -> " . go 0 typ2 . strstr ")"
    raw prec (TyApp typ1 typ2)
        | prec <= 1 = go 1 typ1 . strstr " " . go 2 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " " . go 2 typ2 . strstr ")"
    raw _ (TyCon (TCon typeConstructor _)) = case typeConstructor of
        TC_Named name -> strstr (renderNamedIdentifier name)
        _ -> showsPrec 0 typeConstructor
    raw prec (TyVar var)
        = strstr "#" . showsPrec 0 var
    raw prec (TyMTV mtv)
        = case Map.lookup mtv name_env of
            Nothing -> strstr "mtv_" . showsPrec 0 mtv
            Just name -> strstr name

instantiateScheme :: MonadUnique m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateScheme = instantiateSchemeUsing malformed where
    malformed idx count = diagnosticNoLocWith DiagnosticPretty "HolBETA-InvalidTypeScheme"
        [ Z.Doc.text ("Malformed polymorphic type: variable index #" ++ show idx
            ++ " is outside a forall with " ++ show count ++ " binder(s).")
        , Z.Doc.text "This indicates an invalid type declaration or an internal compiler error."
        ]

instantiateSchemeAt :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateSchemeAt mode moduleName sourceLines loc = instantiateSchemeUsing malformed where
    malformed idx count = diagnosticWithModule mode "HolBETA-InvalidTypeScheme" moduleName sourceLines loc
        [ Z.Doc.text ("Malformed type declaration: variable index #" ++ show idx
            ++ " is outside a forall with " ++ show count ++ " binder(s).")
        , Z.Doc.text "Check the declaration's quantified type variables."
        ]

instantiateSchemeUsing :: MonadUnique m => (Int -> Int -> ErrMsg) -> PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
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
            TyApp typ1 typ2 -> TyApp <$> instantiateBody replacements typ1 <*> instantiateBody replacements typ2
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
    go (Lam (loc, typ) var h term) = Lam (loc, substMTVars theta typ) var h (go term)

mkTyErr :: DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> Map.Map MetaTVar LargeId -> SLoc -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkTyErr mode moduleName source_lines db used_mtvs loc ((actual_typ, expected_typ), typ_error)
    = diagnosticWithModule mode "HolBETA-TypeError" moduleName source_lines loc
        [ text "Context: type mismatch while checking a function application."
        , text ("Expected: `" ++ ty expected_typ ++ "'")
        , text ("Actual:   `" ++ ty actual_typ ++ "'")
        , text ("Reason: " ++ reason)
        ]
    where
        text = Z.Doc.text
        reason = case typ_error of
            KindsAreMismatched (_, kin1) (_, kin2) ->
                "kind mismatch: `" ++ pprint 0 kin1 "' vs `" ++ pprint 0 kin2 "'."
            OccursCheckFailed mtv typ ->
                "occurs check failed; `" ++ ty (TyMTV mtv) ++ "' would contain `" ++ ty typ ++ "'."
            TypesAreMismatched typ1 typ2 ->
                "`" ++ ty typ1 ++ "' is not unifiable with `" ++ ty typ2 ++ "'."
            MalformedTypeApplication typ ->
                "malformed type application `" ++ ty typ ++ "'."
        ty :: MonoType Int -> String
        ty typ = showMonoType db used_mtvs typ ""

mkApplicationTyErr :: DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> Map.Map MetaTVar LargeId -> SLoc -> SLoc -> SLoc -> Bool -> MonoType Int -> MonoType Int -> MonoType Int -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkApplicationTyErr mode moduleName sourceLines db usedMTVs appLoc functionLoc argumentLoc isSelf actualFunction actualArgument resultType mismatch@(_, typError)
    | isSelf && isOccursFailure typError
    = emit appLoc
        [ text "Self-application requires an infinite type."
        , text ("Actual:   `" ++ ty selfActual ++ "'")
        , text ("Required: `" ++ ty selfRequired ++ "'")
        , text "A value cannot be applied to itself in this simply typed language."
        ]
    | not (isFunctionType actualFunction) && not (isMetaType actualFunction)
    = emit functionLoc
        [ text "Cannot apply a non-function value."
        , text ("Actual:   `" ++ ty actualFunction ++ "'")
        , text ("Expected: `" ++ ty requiredFunction ++ "'")
        , text "The expression in function position must have a function type."
        ]
    | Just (expectedArgument, _) <- viewArrow actualFunction
    , typesDefinitelyDisagree expectedArgument actualArgument
    = emit argumentLoc
        [ text "Function argument has the wrong type."
        , text ("Expected: `" ++ ty expectedArgument ++ "'")
        , text ("Actual:   `" ++ ty actualArgument ++ "'")
        ]
    | otherwise
    = mkTyErr mode moduleName sourceLines db usedMTVs argumentLoc mismatch
    where
        text = Z.Doc.text
        emit loc = diagnosticWithModule mode "HolBETA-TypeError" moduleName sourceLines loc
        ty typ = showMonoType db usedMTVs typ ""
        requiredFunction = actualArgument `mkTyArrow` resultType
        viewArrow (TyApp (TyApp (TyCon (TCon TC_Arrow _)) domain) codomain) = Just (domain, codomain)
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
        typesDefinitelyDisagree (TyCon con1) (TyCon con2) = con1 /= con2
        typesDefinitelyDisagree (TyApp f1 a1) (TyApp f2 a2) =
            typesDefinitelyDisagree f1 f2 || typesDefinitelyDisagree a1 a2
        typesDefinitelyDisagree (TyApp _ _) (TyCon _) = True
        typesDefinitelyDisagree (TyCon _) (TyApp _ _) = True

mkSharedVariableTyErr :: DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> Map.Map MetaTVar LargeId -> SLoc -> SLoc -> MonoType Int -> MonoType Int -> ErrMsg
mkSharedVariableTyErr mode moduleName sourceLines db usedMTVs earlierLoc conflictingLoc earlierType conflictingType =
    diagnosticWithModule mode "HolBETA-TypeError" moduleName sourceLines conflictingLoc
        [ text heading
        , text ("Earlier use at " ++ loc earlierLoc ++ " requires:     `" ++ ty earlierType ++ "'")
        , text ("Conflicting use at " ++ loc conflictingLoc ++ " requires: `" ++ ty conflictingType ++ "'")
        , text "Every occurrence of a logic variable in one expression must have the same type."
        ]
    where
        text = Z.Doc.text
        ty typ = showMonoType db usedMTVs typ ""
        loc sourceLoc = pprint 0 sourceLoc ""
        heading = case sourceTextAt sourceLines conflictingLoc of
            Just name -> "Logic variable `" ++ name ++ "' has conflicting type requirements."
            Nothing -> "The same logic variable has conflicting type requirements."

sourceTextAt :: SourceLines -> SLoc -> Maybe String
sourceTextAt (Just sourceLines) (SLoc (row, col) (endRow, endCol))
    | row > 0 && col > 0 && row == endRow && endCol >= col = case drop (row - 1) sourceLines of
        sourceLine : _ -> case take (endCol - col + 1) (drop (col - 1) sourceLine) of
            [] -> Nothing
            sourceText -> Just sourceText
        [] -> Nothing
sourceTextAt _ _ = Nothing

mkExpectedTyErr :: DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> Map.Map MetaTVar LargeId -> SLoc -> MonoType Int -> MonoType Int -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkExpectedTyErr mode moduleName sourceLines db usedMTVs loc actualType expectedType (_, typError) =
    diagnosticWithModule mode "HolBETA-TypeError" moduleName sourceLines loc
        ( [ text "Expression has the wrong result type."
          , text ("Expected: `" ++ ty expectedType ++ "'")
          , text ("Actual:   `" ++ ty actualType ++ "'")
          ]
          ++ goalHint
          ++ reasonLine typError
        )
    where
        text = Z.Doc.text
        ty typ = showMonoType db usedMTVs typ ""
        goalHint
            | expectedType == mkTyO =
                [ text "Hint: a query or fact must have proposition type `o'."
                , text "      Apply a predicate or add a comparison if a proposition was intended."
                ]
            | otherwise = []
        reasonLine (KindsAreMismatched (_, kin1) (_, kin2)) =
            [text ("Reason: kind mismatch (`" ++ pprint 0 kin1 "' vs `" ++ pprint 0 kin2 "').")]
        reasonLine (OccursCheckFailed mtv typ) =
            [text ("Reason: occurs check failed; `" ++ ty (TyMTV mtv) ++ "' would contain `" ++ ty typ ++ "'.")]
        reasonLine (TypesAreMismatched _ _) = []
        reasonLine (MalformedTypeApplication typ) =
            [text ("Reason: malformed type application `" ++ ty typ ++ "'.")]

inferType :: MonadUnique m => NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferType = inferTypeWithDiagnostic DiagnosticPretty Nothing

inferTypeWithSource :: MonadUnique m => SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferTypeWithSource = inferTypeWithDiagnostic DiagnosticPretty

inferTypeWithDiagnostic :: MonadUnique m => DiagnosticMode -> SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferTypeWithDiagnostic mode = inferTypeWithModule mode Nothing

inferTypeWithModule :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> ExceptT ErrMsg m ((TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar (MonoType Int)), Map.Map MetaTVar LargeId)
inferTypeWithModule mode moduleName source_lines db type_env term = do
    ((inferredTerm, assumptions), usedMTVs) <- runStateT (infer term) Map.empty
    return ((inferredTerm, Map.map assumptionType assumptions), usedMTVs)
  where
    infer :: MonadUnique m => TermExpr DataConstructor SLoc -> StateT (Map.Map MetaTVar SmallId) (ExceptT ErrMsg m) (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), Map.Map IVar TypeAssumption)
    infer (Var loc var) = do
        mtv <- getNewMTV "A"
        return (Var (loc, TyMTV mtv) var, Map.singleton var (TypeAssumption (TyMTV mtv) [loc]))
    infer (Con loc con) = case con of
        DC_ChrL chr -> return (Con (loc, mkTyChr) (con, []), Map.empty)
        DC_NatL nat -> return (Con (loc, mkTyNat) (con, []), Map.empty)
        DC_wc -> do
            var <- getUnique
            mtv <- getNewMTV "A"
            return (Con (loc, TyMTV mtv) (con, []), Map.singleton var (TypeAssumption (TyMTV mtv) [loc]))
        con -> do
            (mtvs, typ) <- case Map.lookup con type_env of
                Nothing -> lift (throwE (mkUnknownConErr mode moduleName source_lines loc con))
                Just scheme -> instantiateSchemeAt mode moduleName source_lines loc scheme
            return (Con (loc, typ) (con, map TyMTV mtvs), Map.empty)
    infer (App loc term1 term2) = do
        (term1', assumptions1) <- infer term1
        (term2', assumptions2) <- infer term2
        mtv <- getNewMTV "A"
        used_mtvs <- get
        let sharedVariables = Set.toList (Map.keysSet assumptions1 `Set.intersection` Map.keysSet assumptions2)
            constraints =
                (FunctionApplicationConstraint, snd (getAnnot term1'), snd (getAnnot term2') `mkTyArrow` TyMTV mtv)
                : map sharedVariableConstraint sharedVariables
            sharedVariableConstraint var =
                let earlierAssumption = assumptions1 Map.! var
                    conflictingAssumption = assumptions2 Map.! var
                in ( SharedVariableConstraint
                        (firstAssumptionLoc (fst (getAnnot term1')) earlierAssumption)
                        (firstAssumptionLoc (fst (getAnnot term2')) conflictingAssumption)
                   , assumptionType earlierAssumption
                   , assumptionType conflictingAssumption
                   )
        let isSelfApplication = case (term1, term2) of
                (Var _ var1, Var _ var2) -> var1 == var2
                _ -> False
            applicationError = mkApplicationTyErr mode moduleName source_lines db used_mtvs loc
                (fst (getAnnot term1')) (fst (getAnnot term2')) isSelfApplication
                (snd (getAnnot term1')) (snd (getAnnot term2')) (TyMTV mtv)
            isOccursFailure (OccursCheckFailed _ _) = True
            isOccursFailure _ = False
        theta <- lift $ catchE (unifyWithProvenance constraints) $ \(origin, requiredEarlier, requiredHere, mismatch@(_, typError)) ->
            throwE $ case origin of
                SharedVariableConstraint earlierLoc conflictingLoc
                    | not (isSelfApplication && isOccursFailure typError) ->
                        mkSharedVariableTyErr mode moduleName source_lines db used_mtvs earlierLoc conflictingLoc requiredEarlier requiredHere
                _ -> applicationError mismatch
        let used_mtvs' = used_mtvs `Map.withoutKeys` Map.keysSet (getTypeSubst theta)
            assumptions' = Map.unionWith mergeAssumptions (substMTVars theta assumptions1) (substMTVars theta assumptions2)
        put used_mtvs'
        return (zonkMTV theta (App (loc, TyMTV mtv) term1' term2'), assumptions')
    infer (Lam loc var h term) = do
        (term', assumptions) <- infer term
        case Map.lookup var assumptions of
            Nothing -> do
                mtv <- getNewMTV "A"
                return (Lam (loc, TyMTV mtv `mkTyArrow` snd (getAnnot term')) var h term', assumptions)
            Just assumption -> return (Lam (loc, assumptionType assumption `mkTyArrow` snd (getAnnot term')) var h term', Map.delete var assumptions)
    firstAssumptionLoc _ (TypeAssumption _ (loc : _)) = loc
    firstAssumptionLoc fallback (TypeAssumption _ []) = fallback
    mergeAssumptions earlier conflicting = TypeAssumption
        (assumptionType earlier)
        (assumptionLocs earlier ++ assumptionLocs conflicting)
    mkUnknownConErr :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> DataConstructor -> ErrMsg
    mkUnknownConErr mode' moduleName' source loc con =
        diagnosticWithModule mode' "HolBETA-NotInScope" moduleName' source loc
            [ Z.Doc.text ("Unknown predicate or constructor " ++ renderDataConstructor con ++ ".")
            , Z.Doc.text "No type declaration for this name is visible here."
            , Z.Doc.text "Declare it with `type', import its module, or check the spelling."
            ]
      where
        renderDataConstructor (DC_Named name)
            | isReservedNamedIdentifier name = renderNamedIdentifier name
        renderDataConstructor dataConstructor =
            "`" ++ showsPrec 0 dataConstructor "'"

checkType :: MonadUnique m => NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkType = checkTypeWithDiagnostic DiagnosticPretty Nothing

checkTypeWithSource :: MonadUnique m => SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkTypeWithSource = checkTypeWithDiagnostic DiagnosticPretty

checkTypeWithDiagnostic :: MonadUnique m => DiagnosticMode -> SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkTypeWithDiagnostic mode = checkTypeWithModule mode Nothing

checkTypeWithModule :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> TypeEnv -> TermExpr DataConstructor SLoc -> MonoType Int -> ExceptT ErrMsg m (TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int), (Map.Map MetaTVar LargeId, Map.Map IVar (MonoType Int)))
checkTypeWithModule mode moduleName source_lines db type_env term expected_typ = do
    ((term', assumptions), used_mtvs) <- inferTypeWithModule mode moduleName source_lines db type_env term
    let actual_typ = snd (getAnnot term')
    theta <- catchE (actual_typ ->> expected_typ) $ throwE . mkExpectedTyErr mode moduleName source_lines db used_mtvs (getAnnot term) actual_typ expected_typ
    let used_mtvs' = used_mtvs `Map.withoutKeys` Map.keysSet (getTypeSubst theta)
        assumptions' = substMTVars theta assumptions
    return (zonkMTV theta term', (used_mtvs', assumptions'))
