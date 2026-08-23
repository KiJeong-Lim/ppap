module Hol.BETA.Desugarer where

import Hol.BETA.Compiler (convertQuery)
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.Notation (NotationDB, FixityKind (..), ExpansionDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.PlanHolLexer
import Hol.BETA.TermNode (TermNode, LogicVar (..), freshenName, mkLVar)
import Hol.BETA.TypeChecker (inferTypeWithModule)
import Control.Monad (unless, when)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Z.Doc
import Z.Utils

desugarErr :: DiagnosticMode -> SourceLines -> SLoc -> String -> ErrMsg
desugarErr mode sourceLines loc msg =
    diagnosticWith mode "HolBETA-DesugarError" sourceLines loc [Z.Doc.text msg]

desugarErrInModule :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> ErrMsg
desugarErrInModule mode moduleName sourceLines loc msg =
    diagnosticWithModule mode "HolBETA-DesugarError" moduleName sourceLines loc [Z.Doc.text msg]

makeKindEnv :: DiagnosticMode -> SourceLines -> [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
makeKindEnv mode = makeKindEnvInModule mode Nothing

makeKindEnvInModule :: DiagnosticMode -> Maybe String -> SourceLines -> [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
makeKindEnvInModule mode moduleName sourceLines = go where
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
            then Left (desugarErrInModule mode moduleName sourceLines loc "Higher-order kinds are not supported; expected a kind of rank at most 1.")
            else return kin
    go :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
    go [] kind_env = return kind_env
    go ((loc, (tcon, krep)) : triples) kind_env
        | TC_Named [] <- tcon = Left (desugarErrInModule mode moduleName sourceLines loc "A type-constructor name must not be empty.")
        | TC_Named (tc : _) <- tcon, tc `elem` ['A' .. 'Z'] = Left (desugarErrInModule mode moduleName sourceLines loc "A type-constructor name must start with a lowercase letter.")
        | otherwise = case Map.lookup tcon kind_env of
            Just _ -> Left (desugarErrInModule mode moduleName sourceLines loc ("Type constructor `" ++ showsPrec 0 tcon "' is already declared."))
            Nothing -> do
                kin <- unRep krep
                go triples (Map.insert tcon kin kind_env)

typeRepToMono :: DiagnosticMode -> SourceLines -> KindEnv -> TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
typeRepToMono mode = typeRepToMonoInModule mode Nothing

typeRepToMonoInModule :: DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
typeRepToMonoInModule mode moduleName sourceLines kind_env = go where
    applyModusPonens :: KindExpr -> KindExpr -> Either ErrMsg KindExpr
    applyModusPonens (kin1 `KArr` kin2) kin3
        | kin1 == kin3 = Right kin2
    applyModusPonens (kin1 `KArr` kin2) kin3
        = Left ("Kind mismatch: expected `" ++ pprint 0 kin1 ("', but got `" ++ pprint 0 kin3 "'"))
    applyModusPonens Star kin1
        = Left ("Cannot apply a type of kind `*' to an argument of kind `" ++ pprint 0 kin1 "'")
    go :: TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
    go trep = case trep of
        RTyVar loc tvrep -> return (Star, TyVar tvrep)
        RTyCon loc (TC_Named "string") -> return (Star, mkTyList mkTyChr)
        RTyCon loc type_constructor -> case Map.lookup type_constructor kind_env of
            Nothing -> Left (desugarErrInModule mode moduleName sourceLines loc ("The type constructor `" ++ showsPrec 0 type_constructor "' has not been declared."))
            Just kin -> return (kin, TyCon (TCon type_constructor kin))
        RTyApp loc trep1 trep2 -> do
            (kin1, typ1) <- go trep1
            (kin2, typ2) <- go trep2
            case applyModusPonens kin1 kin2 of
                Left msg -> Left (desugarErrInModule mode moduleName sourceLines loc (dropWhile (== ' ') msg ++ "."))
                Right kin -> return (kin, TyApp typ1 typ2)
        RTyPrn loc trep -> go trep

makeTypeEnv :: DiagnosticMode -> SourceLines -> KindEnv -> [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
makeTypeEnv mode = makeTypeEnvInModule mode Nothing

makeTypeEnvInModule :: DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
makeTypeEnvInModule mode moduleName sourceLines kind_env = go where
    unRep = typeRepToMonoInModule mode moduleName sourceLines kind_env
    generalize :: MonoType LargeId -> Maybe PolyType
    generalize typ = Forall tvars <$> indexify typ where
        getFreeTVs :: MonoType LargeId -> [LargeId]
        getFreeTVs (TyVar tvar) = [tvar]
        getFreeTVs (TyCon _) = []
        getFreeTVs (TyApp typ1 typ2) = getFreeTVs typ1 ++ getFreeTVs typ2
        getFreeTVs (TyMTV _) = []
        tvars :: [LargeId]
        tvars = List.nub (getFreeTVs typ)
        indexify :: MonoType LargeId -> Maybe (MonoType Int)
        indexify (TyVar tvar) = TyVar <$> List.elemIndex tvar tvars
        indexify (TyCon tcon) = Just (TyCon tcon)
        indexify (TyApp typ1 typ2) = TyApp <$> indexify typ1 <*> indexify typ2
        indexify (TyMTV mtv) = Just (TyMTV mtv)
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
        | DC_Named [] <- con
        = Left (desugarErrInModule mode moduleName sourceLines loc "A predicate or constructor name must not be empty.")
        | DC_Named (first : _) <- con, first `elem` ['A' .. 'Z']
        = Left (desugarErrInModule mode moduleName sourceLines loc "A predicate or constructor name must start with a lowercase letter.")
        | otherwise
        = case Map.lookup con type_env of
            Nothing -> do
                (kin, typ) <- unRep trep
                if kin == Star then
                    if hasValidHead typ then case generalize typ of
                        Just scheme -> go triples (Map.insert con scheme type_env)
                        Nothing -> Left (desugarErrInModule mode moduleName sourceLines loc "Could not generalize the declaration's type variables.")
                    else
                        Left (desugarErrInModule mode moduleName sourceLines loc ("The head of the type `" ++ showsPrec 0 con "' is invalid."))
                else
                    Left (desugarErrInModule mode moduleName sourceLines loc ("A term declaration must have kind `*', but this type has kind `" ++ pprint 0 kin "'."))
            _ -> Left (desugarErrInModule mode moduleName sourceLines loc ("Predicate or constructor `" ++ showsPrec 0 con "' is already declared."))

desugarTerm :: MonadUnique m => [SmallId] -> TermRep -> StateT (Map.Map LargeId IVar) m (TermExpr DataConstructor SLoc)
desugarTerm _ (R_wc loc1) = do
    return (Con loc1 DC_wc)
desugarTerm _ (RVar loc1 var_rep) = do
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            var <- getUnique
            put (Map.insert var_rep var env)
            return (Var loc1 var)
        Just var -> return (Var loc1 var)
desugarTerm _ (RCon loc1 (DC_Named con)) = do
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

desugarProgram :: MonadUnique m => KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc, Map.Map LargeId IVar), NotationDB, ExpansionDB)
desugarProgram = desugarProgramWithSource Nothing

desugarProgramWithSource :: MonadUnique m => SourceLines -> KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc, Map.Map LargeId IVar), NotationDB, ExpansionDB)
desugarProgramWithSource = desugarProgramWithDiagnostic DiagnosticPretty

desugarProgramWithDiagnostic :: MonadUnique m => DiagnosticMode -> SourceLines -> KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc, Map.Map LargeId IVar), NotationDB, ExpansionDB)
desugarProgramWithDiagnostic mode sourceLines kind_env type_env file_name program0 = desugarProgramWithModule mode Nothing sourceLines kind_env type_env file_name program0

desugarProgramWithModule :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc, Map.Map LargeId IVar), NotationDB, ExpansionDB)
desugarProgramWithModule mode moduleName sourceLines kind_env type_env =
    desugarProgramWithInherited mode moduleName sourceLines kind_env type_env Notation.initial Notation.initialExpansionDB

desugarProgramWithInherited :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> TypeEnv -> NotationDB -> ExpansionDB -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc, Map.Map LargeId IVar), NotationDB, ExpansionDB)
desugarProgramWithInherited mode moduleName sourceLines kind_env type_env inheritedNotation inheritedExpansion file_name program0 = do
    mapM_ validateDeclarationParameters program
    either (throwE . expansionErr mode moduleName sourceLines) return (Notation.validateExpansionDB expansion_db)
    expandedTypes <- sequence
        [ do
            expanded <- either (throwE . expansionErr mode moduleName sourceLines) return (Notation.expandTypeRepChecked expansion_db trep)
            return (loc, (con, expanded))
        | RTypeDecl loc con trep <- program
        ]
    expandedFacts <- sequence
        [ either (throwE . expansionErr mode moduleName sourceLines) return (Notation.expandTermRepChecked expansion_db factRep)
        | RFactDecl _ factRep <- program
        ]
    kind_env' <- either throwE return
        (makeKindEnvInModule mode moduleName sourceLines [ (loc, (tcon, krep)) | RKindDecl loc tcon krep <- program ] kind_env)
    type_env' <- either throwE return
        (makeTypeEnvInModule mode moduleName sourceLines kind_env' expandedTypes type_env)
    notation_db1 <- either throwE return
        (populateTypeFoldEntriesInModule mode moduleName sourceLines kind_env' expansion_db
            (Notation.declaredTypeAbbrevList ownExpansion) notation_db0)
    notation_db <- populateTermFoldEntriesInModule mode moduleName sourceLines type_env' expansion_db
        (Notation.declaredTermNotationList ownExpansion) notation_db1
    facts' <- lift (mapM (flip runStateT Map.empty . desugarTerm []) expandedFacts)
    return (kind_env' `seq` type_env' `seq` facts' `seq` Program { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts', moduleName = file_name }, notation_db, expansion_db)
    where
        program = program0
        ownExpansion = collectExpansions program
        expansion_db = Notation.mergeExpansion inheritedExpansion ownExpansion
        notation_db0 = Notation.merge inheritedNotation (collectNotation program)

        validateDeclarationParameters decl = do
            case declarationName decl of
                Just (loc, declarationKind, name) ->
                    validateDeclarationName loc declarationKind name
                Nothing -> return ()
            case decl of
                RAbbrevDecl loc name params _ ->
                    validateParameters loc "type abbreviation" name params
                RNotationDecl loc name params _ ->
                    validateParameters loc "term notation" name params
                _ -> return ()

        declarationName (RKindDecl loc (TC_Named name) _) =
            Just (loc, "kind", name)
        declarationName (RTypeDecl loc (DC_Named name) _) =
            Just (loc, "type", name)
        declarationName (RFixityDecl loc _ name _) =
            Just (loc, "fixity", name)
        declarationName (RAbbrevDecl loc name _ _) =
            Just (loc, "type abbreviation", name)
        declarationName (RNotationDecl loc name _ _) =
            Just (loc, "term notation", name)
        declarationName _ = Nothing

        validateDeclarationName loc declarationKind name =
            when (startsUpper name) $
                throwE (desugarErrInModule mode moduleName sourceLines loc
                    ("The " ++ declarationKind ++ " declaration name `" ++ name
                        ++ "' starts with an upper-case letter and cannot be referenced as a constructor. "
                        ++ "Use a lower-case, quoted lower-case, or symbolic declaration name."))

        validateParameters loc declarationKind name params = do
            unless (null invalid) $
                throwE (desugarErrInModule mode moduleName sourceLines loc
                    ("Every parameter of " ++ declarationKind ++ " `" ++ name
                        ++ "' must start with an upper-case letter; invalid parameter"
                        ++ plural invalid ++ ": `" ++ List.intercalate "', `" invalid ++ "'."))
            unless (null duplicates) $
                throwE (desugarErrInModule mode moduleName sourceLines loc
                    ("The parameter list of " ++ declarationKind ++ " `" ++ name
                        ++ "' contains duplicate parameter" ++ plural duplicates
                        ++ " `" ++ List.intercalate "', `" duplicates ++ "'."))
            where
                invalid = [ param | param <- params, not (startsUpper param) ]
                duplicates = List.nub
                    [ param
                    | param : remaining <- List.tails params
                    , param `elem` remaining
                    ]
                plural [_] = ""
                plural _ = "s"

        startsUpper (c : _) = c `elem` ['A' .. 'Z']
        startsUpper [] = False

expansionErr :: DiagnosticMode -> Maybe String -> SourceLines -> Notation.ExpansionError -> ErrMsg
expansionErr mode moduleName sourceLines err = case err of
    Notation.TypeExpansionCycle loc names ->
        desugarErrInModule mode moduleName sourceLines loc
            ("Cyclic type abbreviation: " ++ List.intercalate " -> " names ++ ".")
    Notation.TermExpansionCycle loc names ->
        desugarErrInModule mode moduleName sourceLines loc
            ("Cyclic term notation: " ++ List.intercalate " -> " names ++ ".")

populateTypeFoldTable :: DiagnosticMode -> SourceLines -> KindEnv -> ExpansionDB -> NotationDB -> Either ErrMsg NotationDB
populateTypeFoldTable mode = populateTypeFoldTableInModule mode Nothing

populateTypeFoldTableInModule :: DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> ExpansionDB -> NotationDB -> Either ErrMsg NotationDB
populateTypeFoldTableInModule mode moduleName sourceLines kind_env expansion_db =
    populateTypeFoldEntriesInModule mode moduleName sourceLines kind_env expansion_db (Notation.typeAbbrevList expansion_db)

populateTypeFoldEntriesInModule :: DiagnosticMode -> Maybe String -> SourceLines -> KindEnv -> ExpansionDB -> [(SmallId, [LargeId], TypeRep)] -> NotationDB -> Either ErrMsg NotationDB
populateTypeFoldEntriesInModule mode moduleName sourceLines kind_env expansion_db = go where
    go [] db = Right db
    go ((name, params, rhs) : rest) db = do
        expanded <- either (Left . expansionErr mode moduleName sourceLines) Right
            (Notation.expandTypeRepChecked expansion_db rhs)
        (_, monoType) <- typeRepToMonoInModule mode moduleName sourceLines kind_env expanded
        go rest (Notation.addAbbrev name params monoType db)

populateTermFoldTable :: MonadUnique m => DiagnosticMode -> SourceLines -> TypeEnv -> ExpansionDB -> NotationDB -> ExceptT ErrMsg m NotationDB
populateTermFoldTable mode = populateTermFoldTableInModule mode Nothing

populateTermFoldTableInModule :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> TypeEnv -> ExpansionDB -> NotationDB -> ExceptT ErrMsg m NotationDB
populateTermFoldTableInModule mode moduleName sourceLines type_env expansion_db =
    populateTermFoldEntriesInModule mode moduleName sourceLines type_env expansion_db (Notation.termNotationList expansion_db)

populateTermFoldEntriesInModule :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> TypeEnv -> ExpansionDB -> [(SmallId, [LargeId], TermRep)] -> NotationDB -> ExceptT ErrMsg m NotationDB
populateTermFoldEntriesInModule mode moduleName sourceLines type_env expansion_db = go where
    go [] db = return db
    go ((name, params, rhs) : rest) db = do
        expanded <- either (throwE . expansionErr mode moduleName sourceLines) return
            (Notation.expandTermRepChecked expansion_db rhs)
        template <- compileNotationRHS mode moduleName sourceLines db type_env params expanded
        go rest (Notation.addNotation name params template db)

compileNotationRHS :: MonadUnique m => DiagnosticMode -> Maybe String -> SourceLines -> NotationDB -> TypeEnv -> [LargeId] -> TermRep -> ExceptT ErrMsg m TermNode
compileNotationRHS mode moduleName sourceLines db type_env params body = do
    paramIVars <- lift (mapM (\_ -> getUnique) params)
    let initialNameEnv = Map.fromList (zip params paramIVars)
    (typedTerm, freeVars) <- runStateT (desugarTerm [] body) initialNameEnv
    let undeclared = [ name | name <- Map.keys freeVars, name `notElem` params ]
    unless (null undeclared) $
        throwE (desugarErrInModule mode moduleName sourceLines (termRepLoc body)
            ("The notation right-hand side has undeclared free variable" ++ plural undeclared ++ " `" ++ List.intercalate "', `" undeclared ++ "'."))
    ((typedExpr, assumptions), used_mtvs) <- inferTypeWithModule mode moduleName sourceLines db type_env typedTerm
    let nameEnv = Map.fromList [ (ivar, mkLVar (LV_Named pname)) | (pname, ivar) <- zip params paramIVars ]
    convertQuery used_mtvs assumptions nameEnv typedExpr
    where
        plural [_] = ""
        plural _ = "s"

termRepLoc :: TermRep -> SLoc
termRepLoc (R_wc loc) = loc
termRepLoc (RVar loc _) = loc
termRepLoc (RCon loc _) = loc
termRepLoc (RApp loc _ _) = loc
termRepLoc (RAbs loc _ _) = loc
termRepLoc (RPrn loc _) = loc

collectNotation :: [DeclRep] -> NotationDB
collectNotation = List.foldl' step Notation.initial where
    step db (RFixityDecl _ form name prec) = Notation.addFixity name (toKind form) (fromInteger prec) db
    step db _ = db
    toKind FF_InfixL = FK_InfixL
    toKind FF_InfixR = FK_InfixR
    toKind FF_InfixN = FK_InfixN
    toKind FF_Prefix = FK_Prefix

collectExpansions :: [DeclRep] -> ExpansionDB
collectExpansions = List.foldl' step Notation.initialExpansionDB where
    step db (RAbbrevDecl _ name params body) = Notation.addTypeAbbrevDecl name params body db
    step db (RNotationDecl _ name params body) = Notation.addTermNotationDecl name params body db
    step db _ = db

desugarQuery :: MonadUnique m => TermRep -> ExceptT ErrMsg m (TermExpr DataConstructor SLoc, Map.Map LargeId IVar)
desugarQuery query0 = runStateT (desugarTerm [] query0) Map.empty
