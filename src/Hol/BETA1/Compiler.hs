module Hol.BETA1.Compiler where

import Hol.BETA1.Constant
import Hol.BETA1.Header
import Hol.BETA1.TermNode
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

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> TermNode
convertVar var_name_env env var
    = case var `List.elemIndex` env of
        Nothing -> var_name_env Map.! var
        Just idx -> mkNIdx idx

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) = mkNApp (convertType var_name_env env typ1) (convertType var_name_env env typ2)
convertType var_name_env env (TyCon (TCon tc _)) = mkNCon tc
convertType var_name_env env _ = error "`convertType\'"

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> DataConstructor -> [MonoType Int] -> TermNode
convertCon var_name_env env con tapps = List.foldl' mkNApp (mkNCon con) (map (convertType var_name_env env) tapps)

convertWithoutChecking :: MonadUnique m => FreeVariableEnv -> DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking var_name_env = go where
    loop :: DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermNode
    loop env (Con loc (DC_LO logical_operator, tapps)) = mkNCon logical_operator
    loop env (Var loc var) = convertVar var_name_env env var
    loop env (Con loc (data_constructor, tapps)) = convertCon var_name_env env data_constructor tapps
    loop env (App loc term1 term2) = mkNApp (loop env term1) (loop env term2)
    -- §3.4 CMTT: the typechecker annotates each `Lam` with the lambda's
    -- full type (`T1 -> T2`). The bound variable's type is the domain
    -- `T1`. We thread it through so the runtime can recover the type
    -- of any LV/DC introduced by `pi`/`sigma`/`ty_pi` elimination.
    loop env (Lam (_, lamTy) var1 hint term2) =
        let domTy = case lamTy of
                TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) _ -> LamType (Just t1)
                _ -> noLamType
        in mkNLamHintTy hint domTy (loop (var1 : env) term2)
    go :: MonadUnique m => DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env = return . loop env . reduceTermExpr

convertProgram :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertProgram used_mtvs assumptions = fmap makeUniversalClosure . convertWithoutChecking Map.empty initialEnv where
    initialEnv :: DeBruijnIndicesEnv
    initialEnv = Set.toList (Map.keysSet assumptions `Set.union` Map.keysSet used_mtvs)
    -- §3.4 CMTT: wrap `body` in n `LO_pi` lambdas (one per assumption)
    -- with the assumption's type, then m `LO_ty_pi` lambdas (one per
    -- used_mtv). Innermost lambda binds the smallest IVar so de Bruijn
    -- indices line up with `initialEnv`'s ascending key order. `foldr`
    -- over `toDescList` puts the smallest key last, which becomes the
    -- innermost binder. Each `LO_ty_pi` binder carries `TyMTV mtv` in
    -- its LamType slot as a marker — `Runtime.instantiateFact` reads
    -- this key when peeling the binder and rewrites every `TyMTV mtv`
    -- reference in the body to point at the freshly minted `LV_ty_var`.
    -- The marker means runtime D/G are monotyped (no `TyMTV` left).
    makeUniversalClosure :: TermNode -> TermNode
    makeUniversalClosure body =
        let wrapAssumption (_, ty) acc = mkNApp (mkNCon LO_pi) (mkNLamHintTy Nothing (mkLamType ty) acc)
            wrapTyVar (mtv, _) acc = mkNApp (mkNCon LO_ty_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv)) acc)
            afterAssumed = foldr wrapAssumption body (Map.toDescList assumptions)
        in foldr wrapTyVar afterAssumed (Map.toDescList used_mtvs)

replaceWildcards :: MonadUnique m => TermNode -> m TermNode
replaceWildcards (NCon (DC DC_wc)) = fmap (\u -> mkLVar (LV_Unique u noHint)) getUnique
replaceWildcards (NApp t1 t2) = liftM2 mkNApp (replaceWildcards t1) (replaceWildcards t2)
replaceWildcards (NLam h ty t) = fmap (mkNLamHintTy h ty) (replaceWildcards t)
replaceWildcards t = return t

convertQuery :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertQuery used_mtvs assumptions var_name_env query = do
    node <- if Map.null used_mtvs then
            convertWithoutChecking var_name_env [] query
        else do
            -- §3.4 CMTT: each unsolved meta is bound to a fresh
            -- `LV_ty_var uni` so type-level occurrences in the query
            -- get reified through `convertType`. The same `(mtv, uni)`
            -- pairs also drive `substTyMTV` over the converted body
            -- so polymorphic pi/sigma binders' LamType annotations
            -- carry monotyped `TC_Unique uni` instead of `TyMTV mtv`.
            -- This mirrors the fact side's `instantiateFact LO_ty_pi`
            -- treatment — both paths produce monotyped runtime terms.
            extra_env <- sequence
                [ do
                    uni <- getUnique
                    return (mtv, uni)
                | (mtv, small_id) <- Map.toDescList used_mtvs
                ]
            let var_name_env' = foldr (\(mtv, uni) env -> Map.insert mtv (LVar (LV_ty_var uni)) env) var_name_env extra_env
            node0 <- convertWithoutChecking var_name_env' [] query
            return (foldr (uncurry substTyMTV) node0 extra_env)
    lift (replaceWildcards node)

viewLam :: TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
viewLam = go [] where
    go :: [IVar] -> TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
    go vars (Lam annot var _h term) = go (var : vars) term
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

reduceTermExpr :: TermExpr dcon annot -> TermExpr dcon annot
reduceTermExpr = go Map.empty where
    go :: Map.Map IVar (TermExpr tapp annot) -> TermExpr tapp annot -> TermExpr tapp annot
    go mapsto (App annot1 (Lam annot2 var _h term1) term2)
        = go mapsto (go (Map.singleton var term2) term1)
    go mapsto (Var annot var)
        = case Map.lookup var mapsto of
            Nothing -> Var annot var
            Just term -> term
    go mapsto (Con annot con)
        = Con annot con
    go mapsto (App annot term1 term2)
        = App annot (go mapsto term1) (go mapsto term2)
    go mapsto (Lam annot var h term)
        = Lam annot var h (go mapsto term)
