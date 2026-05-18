module Hol.BETA2.Desugarer where

import Hol.BETA2.Compiler (convertQuery)
import Hol.BETA2.Header
import Hol.BETA2.Notation (NotationDB, FixityKind (..), ExpansionDB)
import qualified Hol.BETA2.Notation as Notation
import Hol.BETA2.PlanHolLexer
import Hol.BETA2.TermNode (TermNode, LogicVar (..), freshenName, mkLVar)
import Hol.BETA2.TypeChecker (inferType)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

makeKindEnv :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
makeKindEnv = go where
    getRank :: KindExpr -> Int
    getRank Star = 0
    getRank (kin1 `KArr` kin2) = max (getRank kin1 + 1) (getRank kin2)
    unRep :: KindRep -> Either ErrMsg KindExpr
    unRep krep = do
        (kin, loc) <- case krep of
            RStar loc -> return (Star, loc)
            RKArr loc krep1 krep2 -> do
                kin1 <- unRep krep1
                kin2 <- unRep krep2
                return (kin1 `KArr` kin2, loc)
            RKPrn loc krep -> do
                kin <- unRep krep
                return (kin, loc)
        if getRank kin > 1
            then Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? the higher-order kind expression is not allowed.")
            else return kin
    go :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
    go [] kind_env = return kind_env
    go ((loc, (tcon, krep)) : triples) kind_env
        | TC_Named tc <- tcon, head tc `elem` ['A' .. 'Z'] = Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? the identifier of a type constructor must be started with a small letter.")
        | otherwise = case Map.lookup tcon kind_env of
            Just _ -> Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? it is wrong to redeclare an already declared type construtor.")
            Nothing -> do
                kin <- unRep krep
                go triples (Map.insert tcon kin kind_env)

-- §2.7 fold table population also needs to lift a TypeRep into a
-- (KindExpr, MonoType LargeId) pair; that path is shared with
-- makeTypeEnv via this top-level helper.
typeRepToMono :: KindEnv -> TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
typeRepToMono kind_env = go where
    applyModusPonens :: KindExpr -> KindExpr -> Either ErrMsg KindExpr
    applyModusPonens (kin1 `KArr` kin2) kin3
        | kin1 == kin3 = Right kin2
    applyModusPonens (kin1 `KArr` kin2) kin3
        = Left ("  ? couldn't solve `" ++ pprint 0 kin1 ("\' ~ `" ++ pprint 0 kin3 "\'"))
    applyModusPonens Star kin1
        = Left ("  ? coudln't solve `type\' ~ `" ++ pprint 1 kin1 " -> _\'")
    go :: TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
    go trep = case trep of
        RTyVar loc tvrep -> return (Star, TyVar tvrep)
        RTyCon loc (TC_Named "string") -> return (Star, mkTyList mkTyChr)
        RTyCon loc type_constructor -> case Map.lookup type_constructor kind_env of
            Nothing -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? the type constructor `" ++ showsPrec 0 type_constructor "hasn't declared.\n"))
            Just kin -> return (kin, TyCon (TCon type_constructor kin))
        RTyApp loc trep1 trep2 -> do
            (kin1, typ1) <- go trep1
            (kin2, typ2) <- go trep2
            case applyModusPonens kin1 kin2 of
                Left msg -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n " ++ msg ++ ".\n"))
                Right kin -> return (kin, TyApp typ1 typ2)
        RTyPrn loc trep -> go trep

makeTypeEnv :: KindEnv -> [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
makeTypeEnv kind_env = go where
    unRep = typeRepToMono kind_env
    generalize :: MonoType LargeId -> PolyType
    generalize typ = Forall tvars (indexify typ) where
        getFreeTVs :: MonoType LargeId -> Set.Set LargeId
        getFreeTVs (TyVar tvar) = Set.singleton tvar
        getFreeTVs (TyCon tcon) = Set.empty
        getFreeTVs (TyApp typ1 typ2) = getFreeTVs typ1 `Set.union` getFreeTVs typ2
        getFreeTVs (TyMTV mtv) = Set.empty
        tvars :: [LargeId]
        tvars = Set.toAscList (getFreeTVs typ)
        indexify :: MonoType LargeId -> MonoType Int
        indexify (TyVar tvar) = maybe (error "unreachable!") TyVar $ tvar `List.elemIndex` tvars
        indexify (TyCon tcon) = TyCon tcon
        indexify (TyApp typ1 typ2) = TyApp (indexify typ1) (indexify typ2)
        indexify (TyMTV mtv) = TyMTV mtv
    hasValidHead :: MonoType LargeId -> Bool
    hasValidHead = go2 . go1 where
        go1 :: MonoType LargeId -> MonoType LargeId
        go1 (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = go1 typ2
        go1 typ1 = typ1
        go2 :: MonoType LargeId -> Bool
        go2 (TyCon tcon) = case tcon of
            TCon (TC_Named "char") _ -> False
            TCon (TC_Named "list") _ -> False
            TCon (TC_Named "nat") _ -> False
            _ -> True
        go2 (TyApp typ _) = go2 typ
        go2 _ = False
    go :: [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
    go [] type_env
        = return type_env
    go ((loc, (con, trep)) : triples) type_env
        = case Map.lookup con type_env of
            Nothing -> do
                (kin, typ) <- unRep trep
                if kin == Star then
                    if hasValidHead typ then
                        go triples (Map.insert con (generalize typ) type_env)
                    else
                        Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? the head of the type `" ++ showsPrec 0 con "\' is invalid."))
                else
                    Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? couldn't solve `" ++ pprint 0 kin "\' ~ `type\'."))
            _ -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? it is wrong to redeclare the already declared constant `" ++ showsPrec 0 con "\'."))

-- §4.5.1: the `live` argument tracks the *stored hints* of every
-- enclosing binder at the current desugaring position. A fresh
-- binder may reuse its source name only when that name does not
-- collide with `live`; otherwise the stored hint is freshened via
-- `freshenName` (§4.5.2). Source-name resolution still binds the
-- original spelling — only the stored hint changes — so the
-- name-resolution `Map.Map LargeId IVar` keeps using `var_rep`.
desugarTerm :: MonadUnique m => [SmallId] -> TermRep -> StateT (Map.Map LargeId IVar) m (TermExpr DataConstructor SLoc)
desugarTerm _    (R_wc loc1) = do
    return (Con loc1 DC_wc)
desugarTerm _    (RVar loc1 var_rep) = do
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            var <- getUnique
            put (Map.insert var_rep var env)
            return (Var loc1 var)
        Just var -> return (Var loc1 var)
desugarTerm _    (RCon loc1 (DC_Named con)) = do
    env <- get
    case Map.lookup con env of
        Nothing -> return (Con loc1 (DC_Named con))
        Just var -> return (Var loc1 var)
desugarTerm _    (RCon loc1 con) = return (Con loc1 con)
desugarTerm live (RApp loc1 term_rep_1 term_rep_2) = do
    term_1 <- desugarTerm live term_rep_1
    term_2 <- desugarTerm live term_rep_2
    return (App loc1 term_1 term_2)
desugarTerm live (RAbs loc1 var_rep term_rep) = do
    let storedHint = if var_rep `notElem` live then var_rep else freshenName var_rep live
    var <- getUnique
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            put (Map.insert var_rep var env)
            term <- desugarTerm (storedHint : live) term_rep
            modify (Map.delete var_rep)
            return (Lam loc1 var (Just storedHint) term)
        Just var' -> do
            put (Map.insert var_rep var (Map.delete var_rep env))
            term <- desugarTerm (storedHint : live) term_rep
            modify (Map.insert var_rep var' . Map.delete var_rep)
            return (Lam loc1 var (Just storedHint) term)
desugarTerm live (RPrn loc1 term_rep) = desugarTerm live term_rep

-- §2.5: a multi-head clause `h_1 & ... & h_n :- body.` is surface sugar
-- for n independent `h_i :- body.` clauses. The body is *cloned* into each
-- clause; downstream `desugarTerm` runs with a fresh name-env per RFactDecl,
-- so logic variables inside the cloned body are freshened per clause
-- (§4.5.1 freshening invariant) and head-level vars share types with body-level
-- vars within their own clause but not across clauses. The unit form
-- `h_1 & ... & h_n.` desugars analogously to n unit facts.
expandMultiHead :: DeclRep -> [DeclRep]
expandMultiHead (RMultiHeadFactDecl loc heads mbody) =
    [ case mbody of
        Just body -> RFactDecl loc (RApp loc (RApp loc (RCon loc (DC_LO LO_if)) h) body)
        Nothing   -> RFactDecl loc h
    | h <- heads
    ]
expandMultiHead decl = [decl]

desugarProgram :: MonadUnique m => KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc), NotationDB, ExpansionDB)
desugarProgram kind_env type_env file_name program0
    = let program = concatMap expandMultiHead program0
          expansion_db = collectExpansions program
          notation_db0 = collectNotation program
          expandedTypes = [ (loc, (con, Notation.expandTypeRep expansion_db trep)) | RTypeDecl loc con trep <- program ]
          expandedFacts = [ Notation.expandTermRep expansion_db fact_rep | RFactDecl _ fact_rep <- program ]
      in case makeKindEnv [ (loc, (tcon, krep)) | RKindDecl loc tcon krep <- program ] kind_env of
            Left err_msg -> throwE err_msg
            Right kind_env' -> case makeTypeEnv kind_env' expandedTypes type_env of
                Left err_msg -> throwE err_msg
                Right type_env' -> case populateTypeFoldTable kind_env' expansion_db notation_db0 of
                    Left err_msg -> throwE err_msg
                    Right notation_db1 -> do
                        notation_db <- populateTermFoldTable type_env' expansion_db notation_db1
                        facts' <- lift (mapM (fmap fst . flip runStateT Map.empty . desugarTerm []) expandedFacts)
                        return (kind_env' `seq` type_env' `seq` facts' `seq` Program { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts', moduleName = file_name }, notation_db, expansion_db)

-- §2.7 fold table seeding (type level only — term level needs the
-- type checker for RHS desugaring and is deferred). For every type
-- abbreviation registered in the ExpansionDB, we expand its RHS
-- (so a chained `abbrev wider := list nested.` resolves down to
-- kernel constructors) then lift it through `typeRepToMono` so the
-- result lives in `MonoType LargeId`. `Notation.addAbbrev` compiles
-- that into a TermNode template via `compileTypeTemplate` and
-- appends it to `NotationDB._entries`. The viewer's fold pre-pass
-- (`Notation.foldTermAsNode`) then re-folds expanded subterms back
-- to the user-declared head at display time.
populateTypeFoldTable :: KindEnv -> ExpansionDB -> NotationDB -> Either ErrMsg NotationDB
populateTypeFoldTable kind_env expansion_db = go (Notation.typeAbbrevList expansion_db)
  where
    go [] db = Right db
    go ((name, params, rhs) : rest) db = do
        let expanded = Notation.expandTypeRep expansion_db rhs
        (_, monoType) <- typeRepToMono kind_env expanded
        go rest (Notation.addAbbrev name params monoType db)

-- §2.7 fold table seeding, term level. For every `notation` declaration
-- registered in the ExpansionDB, we run the same pipeline that compiles
-- a query: expand → desugar (with the declared parameters pre-bound to
-- fresh IVars so they survive name resolution) → `inferType` (the RHS
-- type is free, so we never commit it to a specific shape) → `convertQuery`
-- with each parameter IVar mapped to `LV_Named <param>`. The resulting
-- TermNode template carries the parameters as `LV_Named` leaves, which
-- is exactly the shape `Notation.matchTerm` looks for at fold time.
-- A notation whose RHS fails any of these steps (ill-typed body, unknown
-- constructor, etc.) is silently dropped from the fold table — the
-- §1.6.3 expander still expands the body at use sites, so the only loss
-- is a missing display-direction fold. Logging that to the user is a
-- TODO once we have a less invasive surface for "warning, but not error".
populateTermFoldTable :: MonadUnique m => TypeEnv -> ExpansionDB -> NotationDB -> ExceptT ErrMsg m NotationDB
populateTermFoldTable type_env expansion_db db0 = go (Notation.termNotationList expansion_db) db0
  where
    go [] db = return db
    go ((name, params, rhs) : rest) db = do
        let expanded = Notation.expandTermRep expansion_db rhs
        mTemplate <- lift (runExceptT (compileNotationRHS db0 type_env params expanded))
        case mTemplate of
            Left _    -> go rest db
            Right tn  -> go rest (Notation.addNotation name params tn db)

compileNotationRHS
    :: MonadUnique m
    => NotationDB
    -> TypeEnv
    -> [LargeId]
    -> TermRep
    -> ExceptT ErrMsg m TermNode
compileNotationRHS db type_env params body = do
    paramIVars <- lift (mapM (\_ -> getUnique) params)
    let initialNameEnv = Map.fromList (zip params paramIVars)
    (typedTerm, freeVars) <- runStateT (desugarTerm [] body) initialNameEnv
    ((typedExpr, assumptions), used_mtvs) <- inferType db type_env typedTerm
    let nameEnv = Map.fromList
            [ (ivar, mkLVar (LV_Named pname))
            | (pname, ivar) <- Map.toList freeVars
            , pname `elem` params
            ]
    convertQuery used_mtvs assumptions nameEnv typedExpr

-- §1.5: walk the program top-to-bottom, folding every `RFixityDecl`
-- into the `NotationDB`. Order matters — "last declared wins"
-- (§2.7.4) — so a later infixl that shadows an earlier infixr at
-- the same name simply overwrites the entry in `_fixity`. The
-- seed comes from `Notation.initial`, which carries the BETA1
-- built-in defaults (§1.5's fixity table) and the built-in
-- `string := list char` abbreviation. The desugarer's other passes
-- continue to ignore `RFixityDecl` (it is consumed only here).
collectNotation :: [DeclRep] -> NotationDB
collectNotation = List.foldl' step Notation.initial where
    step db (RFixityDecl _ form name prec) = Notation.addFixity name (toKind form) (fromInteger prec) db
    step db _ = db
    toKind FF_InfixL = FK_InfixL
    toKind FF_InfixR = FK_InfixR
    toKind FF_InfixN = FK_InfixN
    toKind FF_Prefix = FK_Prefix

-- §1.6: collect every `abbrev`/`notation` declaration into the
-- ExpansionDB so `Notation.expandTermRep` / `expandTypeRep` can
-- splice their bodies into call sites during desugaring.
-- "Last declared wins" mirrors §2.7.4 — a later `addTypeAbbrevDecl`
-- simply replaces the earlier entry under the same `Map.insert`
-- semantics. The seed is `initialExpansionDB`, which carries the
-- built-in `string := list char` abbreviation (§1.6.5).
collectExpansions :: [DeclRep] -> ExpansionDB
collectExpansions = List.foldl' step Notation.initialExpansionDB where
    step db (RAbbrevDecl _ name params body) = Notation.addTypeAbbrevDecl name params body db
    step db (RNotationDecl _ name params body) = Notation.addTermNotationDecl name params body db
    step db _ = db

desugarQuery :: MonadUnique m => TermRep -> ExceptT ErrMsg m (TermExpr DataConstructor SLoc, Map.Map LargeId IVar)
desugarQuery query0 = runStateT (desugarTerm [] query0) Map.empty
