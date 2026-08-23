module Hol.ALPHA2.Compiler where

import Hol.ALPHA2.Constant
import Hol.ALPHA2.Header
import Hol.ALPHA2.TermNode
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type ExpectedAs = String

type DeBruijnIndicesEnv = [Unique]

type FreeVariableEnv = Map.Map Unique TermNode

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> Either ErrMsg TermNode
convertVar var_name_env env var
    = case var `List.elemIndex` env of
        Nothing -> case Map.lookup var var_name_env of
            Just term -> return term
            Nothing -> Left ("*** compiler-error: unbound internal variable #" ++ show (unUnique var) ++ ".")
        Just idx -> return (mkNIdx idx)

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> Either ErrMsg TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) =
    liftM2 mkNApp (convertType var_name_env env typ1) (convertType var_name_env env typ2)
convertType _ _ (TyCon (TCon tc _)) = return (mkNCon tc)
convertType _ _ (TyVar idx) = Left
    ("*** compiler-error: unresolved quantified type variable #" ++ show idx ++ ".")

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> DataConstructor -> [MonoType Int] -> Either ErrMsg TermNode
convertCon var_name_env env con tapps = do
    converted <- mapM (convertType var_name_env env) tapps
    return (List.foldl' mkNApp (mkNCon con) converted)

convertWithoutChecking :: MonadUnique m => FreeVariableEnv -> DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking var_name_env = go where
    loop :: DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> Either ErrMsg TermNode
    loop _ (Con _ (DC_LO logical_operator, _)) = return (mkNCon logical_operator)
    loop env (Var (loc, _) var) =
        withCompilerLocation loc (convertVar var_name_env env var)
    loop env (Con (loc, _) (data_constructor, tapps)) =
        withCompilerLocation loc (convertCon var_name_env env data_constructor tapps)
    loop env (App _ term1 term2) = liftM2 mkNApp (loop env term1) (loop env term2)
    loop env (Lam _ var1 term2) = fmap mkNLam (loop (var1 : env) term2)
    go :: MonadUnique m => DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env term = case loop env (reduceTermExpr term) of
        Left err -> throwE err
        Right converted -> return converted

-- The low-level conversion helpers retain their long-standing, location-free
-- API.  At the annotated expression boundary, attach the exact occurrence
-- which exposed the malformed internal term or type.
withCompilerLocation :: SLoc -> Either ErrMsg a -> Either ErrMsg a
withCompilerLocation loc = either (Left . compilerErrorAt loc) Right

compilerErrorAt :: SLoc -> ErrMsg -> ErrMsg
compilerErrorAt loc err = concat
    [ "*** compiler-error[", pprint 0 loc "]:\n"
    , "  ", detail, "\n"
    ]
  where
    detail = case List.stripPrefix "*** compiler-error: " err of
        Just message -> message
        Nothing -> err

convertProgram :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertProgram used_mtvs assumptions = fmap makeUniversalClosure . convertWithoutChecking Map.empty initialEnv where
    initialEnv :: DeBruijnIndicesEnv
    initialEnv = Set.toList (Map.keysSet assumptions `Set.union` Map.keysSet used_mtvs)
    makeUniversalClosure :: TermNode -> TermNode
    makeUniversalClosure = flip (foldr (\_ -> \term -> (mkNApp (mkNCon LO_ty_pi)) (mkNLam term))) [1, 2 .. Map.size used_mtvs] . flip (foldr (\_ -> \term -> mkNApp (mkNCon LO_pi) (mkNLam term))) [1, 2 .. Map.size assumptions]

replaceWildcards :: MonadUnique m => TermNode -> m TermNode
replaceWildcards (NCon (DC DC_wc)) = fmap (mkLVar . LV_Unique) getUnique
replaceWildcards (NApp t1 t2) = liftM2 mkNApp (replaceWildcards t1) (replaceWildcards t2)
replaceWildcards (NLam t) = fmap mkNLam (replaceWildcards t)
replaceWildcards t = return t

convertQuery :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertQuery used_mtvs assumptions var_name_env query = do
    node <- if Map.null used_mtvs then
            convertWithoutChecking var_name_env [] query
        else do
            extra_env <- sequence
                [ do
                    uni <- getUnique
                    return (mtv, LVar (LV_ty_var uni))
                | (mtv, small_id) <- Map.toDescList used_mtvs
                ]
            convertWithoutChecking (foldr (uncurry Map.insert) var_name_env extra_env) [] query
    lift (replaceWildcards node)

viewLam :: TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
viewLam = go [] where
    go :: [IVar] -> TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
    go vars (Lam annot var term) = go (var : vars) term
    go vars term = (vars, term)

unFoldApp :: TermExpr dcon annot -> (TermExpr dcon annot, [TermExpr dcon annot])
unFoldApp = flip go [] where
    go :: TermExpr dcon annot -> [TermExpr dcon annot] -> (TermExpr dcon annot, [TermExpr dcon annot])
    go (App annot term1 term2) terms = go term1 (term2 : terms)
    go term terms = (term, terms)

isPredicate :: MonoType Int -> Bool
isPredicate (TyCon (TCon (TC_Named "o") _)) = True
isPredicate (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = isPredicate typ2
isPredicate _ = False

-- Reject clauses whose executable head would be a variable or a logical /
-- primitive control.  Such a term can have type `o', so typechecking alone is
-- not enough; allowing it through used to make Main.addIndex crash on a valid
-- surface program such as `P.'.
validateProgramFact
    :: TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
    -> Either ErrMsg ()
validateProgramFact = validateClause . reduceTermExpr where
    validateClause term = case unFoldApp term of
        (Con _ (DC_LO LO_and, _), [lhs, rhs]) ->
            validateClause lhs >> validateClause rhs
        (Con _ (DC_LO LO_ty_pi, _), [Lam _ _ body]) -> validateClause body
        (Con _ (DC_LO LO_pi, _), [Lam _ _ body]) -> validateClause body
        (Con _ (DC_LO LO_if, _), [conclusion, premise]) ->
            validateGlobalConclusion conclusion
                >> validateGoal (termVars conclusion) premise
        (Con _ (DC_Named name, _), _)
            | name `notElem` ["print", "read"] -> Right ()
        _ -> Left (invalidClauseMessage (fst (getAnnot term)))

    -- A clause as a whole may contain implication, but the conclusion of one
    -- implication may not itself be another clause.  Keeping these grammars
    -- separate prevents nested heads such as `(p :- q) :- r' from reaching
    -- the runtime indexer as if they were named predicates.
    validateGlobalConclusion term = case unFoldApp term of
        (Con _ (DC_LO LO_and, _), [lhs, rhs]) ->
            validateGlobalConclusion lhs >> validateGlobalConclusion rhs
        (Con _ (DC_LO LO_ty_pi, _), [Lam _ _ body]) ->
            validateGlobalConclusion body
        (Con _ (DC_LO LO_pi, _), [Lam _ _ body]) ->
            validateGlobalConclusion body
        (Con _ (DC_Named name, _), _)
            | name `notElem` ["print", "read"] -> Right ()
        _ -> Left (invalidClauseMessage (fst (getAnnot term)))

    validateGoal anchored term = case unFoldApp term of
        (Con _ (DC_LO LO_and, _), [lhs, rhs]) ->
            validateGoal anchored lhs >> validateGoal anchored rhs
        (Con _ (DC_LO LO_or, _), [lhs, rhs]) ->
            validateGoal anchored lhs >> validateGoal anchored rhs
        (Con _ (DC_LO LO_imply, _), [antecedent, consequent]) ->
            validateLocalClause anchored antecedent >> validateGoal anchored consequent
        (Con _ (DC_LO LO_pi, _), [Lam _ variable body]) ->
            validateGoal (Set.insert variable anchored) body
        (Con _ (DC_LO LO_sigma, _), [Lam _ _ body]) ->
            -- `sigma' creates a flexible variable, not a dispatchable rigid
            -- predicate.  Treating it as an anchor lets `sigma P\ P' reach
            -- Runtime.dispatch with an LVar head and fail as a kernel error.
            validateGoal anchored body
        (Con _ (DC_LO logical, _), args)
            | validControlArity logical (length args) -> Right ()
            | otherwise -> Left (invalidGoalMessage (fst (getAnnot term)))
        (Var loc variable, _)
            | variable `Set.member` anchored -> Right ()
            | otherwise -> Left (invalidGoalMessage (fst loc))
        (Con _ _, _) -> Right ()
        _ -> Left (invalidGoalMessage (fst (getAnnot term)))

    validateLocalClause anchored term = case unFoldApp term of
        (Con _ (DC_LO LO_and, _), [lhs, rhs]) ->
            validateLocalClause anchored lhs >> validateLocalClause anchored rhs
        (Con _ (DC_LO LO_ty_pi, _), [Lam _ variable body]) ->
            validateLocalClause (Set.insert variable anchored) body
        (Con _ (DC_LO LO_pi, _), [Lam _ variable body]) ->
            validateLocalClause (Set.insert variable anchored) body
        (Con _ (DC_LO LO_if, _), [conclusion, premise]) ->
            validateLocalHead anchored conclusion
                >> validateGoal (anchored `Set.union` termVars conclusion) premise
        _ -> validateLocalHead anchored term

    validateLocalHead anchored term = case unFoldApp term of
        (Con _ (DC_Named name, _), _)
            | name `notElem` ["print", "read"] -> Right ()
        (Var _ variable, _)
            | variable `Set.member` anchored -> Right ()
        (Con _ (DC_eq, _), _) -> Right ()
        (Con _ (comparison, _), _)
            | comparison `elem` [DC_ge, DC_gt, DC_le, DC_lt] -> Right ()
        _ -> Left (invalidClauseMessage (fst (getAnnot term)))

    validControlArity logical arity = case logical of
        LO_true -> arity == 0
        LO_fail -> arity == 0
        LO_cut -> arity == 0
        LO_debug -> arity == 1
        LO_is -> arity == 2
        _ -> False

    termVars term = case term of
        Var _ variable -> Set.singleton variable
        Con _ _ -> Set.empty
        App _ lhs rhs -> termVars lhs `Set.union` termVars rhs
        Lam _ variable body -> Set.delete variable (termVars body)

    invalidClauseMessage loc = concat
        [ "*** compiler-error[", pprint 0 loc "]:\n"
        , "  Context: invalid program clause head.\n"
        , "  Reason: a program clause must be headed by a declared, named predicate.\n"
        , "  A logic variable, nested clause, logical control, comparison, or primitive I/O operation cannot be indexed as a fact.\n"
        ]

    invalidGoalMessage loc = concat
        [ "*** compiler-error[", pprint 0 loc "]:\n"
        , "  Context: invalid executable goal in a clause body.\n"
        , "  Reason: a predicate-valued variable must be connected to the clause head\n"
        , "  or introduced by an explicit `pi' or `sigma' binder.\n"
        ]

reduceTermExpr :: TermExpr dcon annot -> TermExpr dcon annot
reduceTermExpr = go Map.empty where
    go :: Map.Map IVar (TermExpr tapp annot) -> TermExpr tapp annot -> TermExpr tapp annot
    go mapsto (App annot1 (Lam annot2 var term1) term2)
        = go mapsto (go (Map.singleton var term2) term1)
    go mapsto (Var annot var)
        = case Map.lookup var mapsto of
            Nothing -> Var annot var
            Just term -> term
    go mapsto (Con annot con)
        = Con annot con
    go mapsto (App annot term1 term2)
        = App annot (go mapsto term1) (go mapsto term2)
    go mapsto (Lam annot var term)
        = Lam annot var (go mapsto term)
