module Hol.BETA.ModuleLoader
    ( ModuleEnv (..)
    , LoadedModule (..)
    , loadMain
    , loadMainWithDiagnostic
    , pathDerivedName
    , validateClauseTerm
    , validateLocalClauseTerm
    , validateGoalTerm
    , polyTypeEq
    ) where

import Hol.BETA.Arith (installPresburgerWithDiagnostic, liftConstraint)
import Hol.BETA.Compiler (convertProgram)
import Hol.BETA.Constant (Constant (..))
import Hol.BETA.Desugarer (collectExpansions, collectNotation, desugarProgramWithInherited)
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.FixityResolver (FixityError (..), resolveDeclsWithFixity)
import Hol.BETA.Notation (NotationDB, ExpansionDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.PlanHolLexer
import Hol.BETA.PlanHolParser (runHolParser)
import Hol.BETA.TermNode (LogicVar, TermNode (..), ReduceOption (NF), getNodeSLoc, rewrite, unfoldlNApp)
import Hol.BETA.TypeChecker (checkTypeWithModule)

import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Z.Doc
import System.Directory (canonicalizePath, doesFileExist, getCurrentDirectory)
import System.FilePath ((</>), isPathSeparator, isRelative, makeRelative, splitDirectories, takeDirectory)
import Z.System.File (readFileNow)
import Z.Utils

data ModuleEnv
    = ModuleEnv
        { moduleEnvName :: String
        , moduleEnvPath :: FilePath
        , moduleEnvKinds :: KindEnv
        , moduleEnvOwnKinds :: KindEnv
        , moduleEnvTypes :: TypeEnv
        , moduleEnvOwnTypes :: TypeEnv
        , moduleEnvFacts :: [TermNode]
        , moduleEnvOwnFacts :: [TermNode]
        , moduleEnvClosure :: [FilePath]
        , moduleEnvNotation :: NotationDB
        , moduleEnvOwnNotation :: NotationDB
        , moduleEnvExpansion :: ExpansionDB
        , moduleEnvOwnExpansion :: ExpansionDB
        , moduleEnvImports :: [String]
        , moduleEnvImportPaths :: [FilePath]
        , moduleEnvWarnings :: [ErrMsg]
        }
    deriving ()

data LoadedModule
    = LoadedModule
        { loadedMain :: ModuleEnv
        , loadedAll :: Map FilePath ModuleEnv
        , loadedOrder :: [String]
        , loadedWarnings :: [ErrMsg]
        }
    deriving ()

data LoaderState
    = LoaderState
        { lsLoaded :: Map FilePath ModuleEnv
        , lsLoading :: [(String, FilePath)]
        , lsOrder :: [String]
        , lsRoot :: FilePath
        , lsInitialKinds :: KindEnv
        , lsInitialTypes :: TypeEnv
        , lsInitialFacts :: [TermNode]
        , lsDiagnosticMode :: DiagnosticMode
        , lsWarnings :: [ErrMsg]
        }
    deriving ()

type Loader m a = ExceptT ErrMsg (State.StateT LoaderState m) a

moduleErr :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> ErrMsg
moduleErr mode moduleName sourceLines loc msg = diagnosticWithModule mode "HolBETA-ModuleError" moduleName sourceLines loc [Z.Doc.text msg]

moduleWarning :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> ErrMsg
moduleWarning mode moduleName sourceLines loc msg = diagnosticWarningWithModule mode "HolBETA-ModuleWarning" moduleName sourceLines loc [Z.Doc.text msg]

pathDerivedName :: FilePath -> FilePath -> String
pathDerivedName root absPath = map dotSep stripped where
    rel = makeRelative root absPath
    stripped = dropDotHol rel
    dotSep c
        | isPathSeparator c = '.'
        | otherwise = c
    dropDotHol p
        | List.isSuffixOf ".hol" p = take (length p - 4) p
        | otherwise                = p

loadMain :: UniqueM m => KindEnv -> TypeEnv -> [TermNode] -> FilePath -> m (Either ErrMsg LoadedModule)
loadMain = loadMainWithDiagnostic DiagnosticPretty

loadMainWithDiagnostic :: UniqueM m => DiagnosticMode -> KindEnv -> TypeEnv -> [TermNode] -> FilePath -> m (Either ErrMsg LoadedModule)
loadMainWithDiagnostic mode initialKinds initialTypes initialFacts mainPath = do
    root <- liftIO getCurrentDirectory
    rootC <- liftIO (canonicalizePath root)
    canonicalMain <- liftIO (canonicalizePath mainPath)
    let st0 = LoaderState { lsLoaded = Map.empty, lsLoading = [], lsOrder = [], lsRoot = rootC, lsInitialKinds = initialKinds, lsInitialTypes = initialTypes, lsInitialFacts = initialFacts, lsDiagnosticMode = mode, lsWarnings = []}
    (eMain, stN) <- State.runStateT (runExceptT (loadFile canonicalMain Nothing)) st0
    case eMain of
        Left err -> return (Left err)
        Right env -> return (Right (LoadedModule { loadedMain  = env , loadedAll = lsLoaded stN, loadedOrder = reverse (lsOrder stN) , loadedWarnings = reverse (lsWarnings stN) }))

loadFile :: UniqueM m => FilePath -> Maybe (FilePath, SLoc, SourceLines) -> Loader m ModuleEnv
loadFile canonicalPath importContext = do
    st <- lift State.get
    let mode = lsDiagnosticMode st
    if not (withinRoot (lsRoot st) canonicalPath) then
        throwE $ case importContext of
            Just (importerPath, loc, sourceLines) -> moduleErr mode (Just importerPath) sourceLines loc
                ("Module path `" ++ canonicalPath ++ "' is outside the project root `" ++ lsRoot st ++ "'.")
            Nothing -> diagnosticNoLocWith mode "HolBETA-ModuleError"
                [Z.Doc.text ("Module path `" ++ canonicalPath ++ "' is outside the project root `" ++ lsRoot st ++ "'.")]
    else case Map.lookup canonicalPath (lsLoaded st) of
        Just env -> return env
        Nothing -> do
            let mname = pathDerivedName (lsRoot st) canonicalPath
            case List.find ((== canonicalPath) . snd) (lsLoading st) of
                Just cycleStart -> do
                    let newer = takeWhile ((/= canonicalPath) . snd) (lsLoading st)
                        cycle = cycleStart : reverse newer ++ [cycleStart]
                        ambiguous (name, path) = any (\(name', path') -> name == name' && path /= path') cycle
                        renderCycleEntry entry@(name, path)
                            | ambiguous entry = name ++ " (" ++ path ++ ")"
                            | otherwise = name
                        chain = List.intercalate " -> " (map renderCycleEntry cycle)
                    throwE $ case importContext of
                        Just (importerPath, loc, sourceLines) -> moduleErr mode (Just importerPath) sourceLines loc ("Import cycle detected: " ++ chain ++ ".")
                        Nothing -> diagnosticNoLocWith mode "HolBETA-ModuleError" [Z.Doc.text ("Import cycle detected: " ++ chain ++ ".")]
                Nothing -> do
                    msrc <- liftIO (readFileNow canonicalPath)
                    case msrc of
                        Nothing -> throwE $ case importContext of
                            Just (importerPath, loc, sourceLines) ->
                                diagnosticWithModule mode "HolBETA-FileError" (Just importerPath) sourceLines loc
                                    [Z.Doc.text ("Cannot read imported module file `" ++ canonicalPath ++ "'.")]
                            Nothing -> diagnosticNoLocWith mode "HolBETA-FileError"
                                [Z.Doc.text ("Cannot read file `" ++ canonicalPath ++ "'.")]
                        Just src -> do
                            let sourceLines = Just (lines src)
                            case runHolLexer src of
                                Left (row, col) -> throwE (diagnosticWithModule mode "HolBETA-LexError" (Just canonicalPath) sourceLines (SLoc (row, col) (row, col)) [Z.Doc.text ("Lexing failed in `" ++ canonicalPath ++ "'.")])
                                Right tokens -> case runHolParser tokens of
                                    Left Nothing -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) sourceLines (eofSLoc src) [Z.Doc.text ("Parsing failed at EOF in `" ++ canonicalPath ++ "'.")])
                                    Left (Just token) -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) sourceLines (getSLoc token) [Z.Doc.text ("Parsing failed in `" ++ canonicalPath ++ "'.")])
                                    Right (Left query) -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) sourceLines (getSLoc query) [Z.Doc.text ("File `" ++ canonicalPath ++ "' is a query, not a program.")])
                                    Right (Right decls0) -> case extractHeaderAndImports mode (Just canonicalPath) sourceLines decls0 of
                                        Left err -> throwE err
                                        Right (mHeader, imports, body0) -> elaborate canonicalPath mname (lines src) mHeader imports body0

withinRoot :: FilePath -> FilePath -> Bool
withinRoot root path = isRelative relative && ".." `notElem` splitDirectories relative where
    relative = makeRelative root path

elaborate :: UniqueM m => FilePath -> String -> [String] -> Maybe (SLoc, String) -> [(SLoc, String)] -> [DeclRep] -> Loader m ModuleEnv
elaborate canonicalPath mname sourceLines mHeader imports body0 = do
    st0 <- lift State.get
    let mode = lsDiagnosticMode st0
    case mHeader of
        Just (loc, declared) | declared /= mname ->
            throwE (moduleErr mode (Just canonicalPath) (Just sourceLines) loc ("Module header `" ++ declared ++ "' does not match file path-derived name `" ++ mname ++ "'."))
        _ -> return ()
    let importWarnings = duplicateImportWarnings mode canonicalPath (Just sourceLines) imports
        importsUnique = uniqueImports imports
        go imp = do
            env <- loadImport canonicalPath (Just sourceLines) imp
            return (imp, env)
    lift (State.modify (\s -> s { lsWarnings = reverse importWarnings ++ lsWarnings s }))
    lift (State.modify (\s -> s { lsLoading = (mname, canonicalPath) : lsLoading s }))
    importedEnvs0 <- mapM go importsUnique
    lift (State.modify (\ s -> s { lsLoading = drop 1 (lsLoading s) }))
    st <- lift State.get
    let importedEnvsWithLocs = uniqueImportedEnvs importedEnvs0
        importedOwnEnvsWithLocs = uniqueImportedEnvs
            [ (directImport, dependencyEnv)
            | (directImport, directEnv) <- importedEnvsWithLocs
            , dependencyPath <- moduleEnvClosure directEnv
            , Just dependencyEnv <- [Map.lookup dependencyPath (lsLoaded st)]
            ]
        initialKinds = lsInitialKinds st
        initialFacts = lsInitialFacts st
        initialTypes = lsInitialTypes st
    (composedKinds, composedTypes, composedNotation, composedExpansion, _origins) <- foldM
        (combineOwnImport mode (Just canonicalPath) (Just sourceLines))
        (initialKinds, initialTypes, Notation.initial, Notation.initialExpansionDB, emptyOrigins)
        importedOwnEnvsWithLocs
    let closureEnvs = map snd importedOwnEnvsWithLocs
        importedClosure = map moduleEnvPath closureEnvs
        importedFacts = concatMap moduleEnvOwnFacts closureEnvs
    body <- case checkOwnFixityAgainstImports composedNotation body0 >> resolveDeclsWithFixity composedNotation body0 of
        Left (FixityError loc msg) -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) (Just sourceLines) loc [Z.Doc.text ("Parsing failed in `" ++ canonicalPath ++ "'."), Z.Doc.text msg])
        Right decls -> return decls
    (env1, ownNotation, ownExpansion) <- desugarProgramWithInherited mode (Just canonicalPath) (Just sourceLines) composedKinds composedTypes composedNotation composedExpansion mname body
    facts2 <- sequence
        [ do
            checked <- checkTypeWithModule mode (Just canonicalPath) (Just sourceLines) ownNotation (_TypeDecls env1) fact mkTyO
            return (factNames, checked)
        | (fact, factNames) <- _FactDecls env1
        ]
    facts3 <- sequence
        [ convertProgram (invertNameEnv factNames) used_mtvs assumptions fact
        | (factNames, (fact, (used_mtvs, assumptions))) <- facts2
        ]
    let factLocs = [ loc | RFactDecl loc _ <- body ]
    ownFactsR <- sequence
        [ do
            installed <- either throwE return (installPresburgerWithDiagnostic mode (Just canonicalPath) (Just sourceLines) fact)
            either throwE return (validateInstalledFact mode canonicalPath (Just sourceLines) loc installed)
            return installed
        | (loc, fact) <- zip factLocs facts3
        ]
    let ownKinds = Map.fromList
            [ (typeConstructor, kind)
            | RKindDecl _ typeConstructor _ <- body
            , Just kind <- [Map.lookup typeConstructor (_KindDecls env1)]
            ]
        ownTypes = Map.fromList
            [ (dataConstructor, scheme)
            | RTypeDecl _ dataConstructor _ <- body
            , Just scheme <- [Map.lookup dataConstructor (_TypeDecls env1)]
            ]
        ownExpansionDelta = collectExpansions body
        ownNotationDelta = Notation.declarationDelta (collectNotation body) ownExpansionDelta ownNotation
        env = ModuleEnv
            { moduleEnvName = mname
            , moduleEnvPath = canonicalPath
            , moduleEnvKinds = _KindDecls env1
            , moduleEnvOwnKinds = ownKinds
            , moduleEnvTypes = _TypeDecls env1
            , moduleEnvOwnTypes = ownTypes
            , moduleEnvFacts = initialFacts ++ importedFacts ++ ownFactsR
            , moduleEnvOwnFacts = ownFactsR
            , moduleEnvClosure = importedClosure ++ [canonicalPath]
            , moduleEnvNotation = ownNotation
            , moduleEnvOwnNotation = ownNotationDelta
            , moduleEnvExpansion = ownExpansion
            , moduleEnvOwnExpansion = ownExpansionDelta
            , moduleEnvImports = [ m | ((_, m), _) <- importedEnvsWithLocs ]
            , moduleEnvImportPaths = map (moduleEnvPath . snd) importedEnvsWithLocs
            , moduleEnvWarnings = importWarnings
            }
    lift (State.modify (\s -> s { lsLoaded = Map.insert canonicalPath env (lsLoaded s), lsOrder  = mname : lsOrder s }))
    return env

invertNameEnv :: Map.Map LargeId IVar -> Map.Map IVar LargeId
invertNameEnv = Map.fromList . map (\(name, ivar) -> (ivar, name)) . Map.toList

loadImport :: UniqueM m => FilePath -> SourceLines -> (SLoc, String) -> Loader m ModuleEnv
loadImport importerPath sourceLines (importLoc, importedName) = do
    st <- lift State.get
    let dir = takeDirectory importerPath
        root = lsRoot st
    mFound <- liftIO (resolveImport dir root importedName)
    case mFound of
        Nothing -> do
            st <- lift State.get
            throwE (moduleErr (lsDiagnosticMode st) (Just importerPath) sourceLines importLoc ("Cannot resolve module `" ++ importedName ++ "' from `" ++ importerPath ++ "'."))
        Just canonical -> loadFile canonical (Just (importerPath, importLoc, sourceLines))

resolveImport :: FilePath -> FilePath -> String -> IO (Maybe FilePath)
resolveImport dir root mname
    = do
        let segs = splitOn '.' mname
            rel = foldr (</>) (last segs ++ ".hol") (init segs)
            candidates = [dir </> rel, root </> rel]
        tryCandidates candidates
    where
        tryCandidates [] = return Nothing
        tryCandidates (p : ps) = do
            ok <- doesFileExist p
            if ok then Just <$> canonicalizePath p else tryCandidates ps

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
    (a, "") -> [a]
    (a, _ : rest) -> a : splitOn c rest

uniqueImports :: [(SLoc, String)] -> [(SLoc, String)]
uniqueImports = reverse . snd . List.foldl' step ([], []) where
    step (seen, acc) imp@(_, name)
        | name `elem` seen = (seen, acc)
        | otherwise = (name : seen, imp : acc)

uniqueImportedEnvs :: [((SLoc, String), ModuleEnv)] -> [((SLoc, String), ModuleEnv)]
uniqueImportedEnvs = reverse . snd . List.foldl' step ([], []) where
    step (seen, acc) imported@(_, env)
        | moduleEnvPath env `elem` seen = (seen, acc)
        | otherwise = (moduleEnvPath env : seen, imported : acc)

duplicateImportWarnings :: DiagnosticMode -> String -> SourceLines -> [(SLoc, String)] -> [ErrMsg]
duplicateImportWarnings mode moduleName sourceLines = go [] where
    go _ [] = []
    go seen ((loc, name) : rest) = if name `elem` seen then moduleWarning mode (Just moduleName) sourceLines loc ("Duplicate import `" ++ name ++ "' ignored.") : go seen rest else go (name : seen) rest

validateInstalledFact :: DiagnosticMode -> FilePath -> SourceLines -> SLoc -> TermNode -> Either ErrMsg ()
validateInstalledFact mode modulePath sourceLines fallback fact =
    case validateClauseTerm fact of
        Right () -> Right ()
        Left bad -> Left (moduleErr mode (Just modulePath) sourceLines (nodeLoc bad)
            "Clause validation failed: program heads must be user-declared named predicates, and a clause conclusion cannot itself contain `:-'. A predicate-variable call in a program body must occur in its conclusion or beneath an explicit `pi' or `sigma' binder. Local heads may additionally use an in-scope predicate parameter. Local comparison assumptions must be bare linear-Presburger constraints. Logical controls, primitive I/O, and unsupported constraints are not clauses.")
    where
        nodeLoc bad = case getNodeSLoc bad of
            Just loc -> loc
            Nothing -> fallback

validateClauseTerm :: TermNode -> Either TermNode ()
validateClauseTerm fact = case unfoldlNApp fact of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) -> validateClauseTerm left >> validateClauseTerm right
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam _ _ body _]) -> validateClauseTerm body
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) -> validateClauseTerm body
    (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) ->
        validateGlobalClauseConclusion conclusion
            >> validateAnchoredGoal (termGoalAnchors conclusion) premise
    (NCon (DC (DC_Named name)) _, _)
        | notElem name primitivePredicateNames -> Right ()
    _ -> Left fact

-- A clause conclusion may contain the same conjunction and universal-prefix
-- structure as a collection of unit heads, but it may not itself contain
-- another clause constructor.  Recursing through 'validateClauseTerm' here
-- would accept `(p :- q) :- r`, index it under `p`, and then install an
-- unusable LO_if-headed clause.
validateGlobalClauseConclusion :: TermNode -> Either TermNode ()
validateGlobalClauseConclusion conclusion = case unfoldlNApp conclusion of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) ->
        validateGlobalClauseConclusion left >> validateGlobalClauseConclusion right
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam _ _ body _]) ->
        validateGlobalClauseConclusion body
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) ->
        validateGlobalClauseConclusion body
    (NCon (DC (DC_Named name)) _, _)
        | notElem name primitivePredicateNames -> Right ()
    _ -> Left conclusion

validateLocalClauseTerm :: TermNode -> Either TermNode ()
validateLocalClauseTerm fact = case unfoldlNApp fact of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) ->
        validateLocalClauseTerm left >> validateLocalClauseTerm right
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam _ _ body _]) -> validateLocalClauseTerm body
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) -> validateLocalClauseTerm body
    (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) ->
        validateLocalClauseConclusion conclusion >> validateGoalTerm premise
    _ | isLocalPredicateHead fact -> Right ()
    (NCon (DC DC_eq) _, _) -> Right ()
    (NCon (DC dataConstructor) _, _)
        | dataConstructor `elem` [DC_ge, DC_gt, DC_le, DC_lt]
        , Just _ <- liftConstraint fact -> Right ()
    (NPresburgerCheck _ _ _, []) -> Right ()
    _ -> Left fact

-- Local clauses may abstract over a predicate (`pi p\\ ...`) and use that
-- rigid predicate parameter as their head.  Such a head is a de Bruijn index
-- before runtime instantiation, rather than a globally named constant.
validateLocalClauseConclusion :: TermNode -> Either TermNode ()
validateLocalClauseConclusion conclusion = case unfoldlNApp conclusion of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) ->
        validateLocalClauseConclusion left >> validateLocalClauseConclusion right
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam _ _ body _]) -> validateLocalClauseConclusion body
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) -> validateLocalClauseConclusion body
    _ | isLocalPredicateHead conclusion -> Right ()
    _ -> Left conclusion

isLocalPredicateHead :: TermNode -> Bool
isLocalPredicateHead term = case fst (unfoldlNApp term) of
    NCon (DC (DC_Named name)) _ -> notElem name primitivePredicateNames
    NCon (DC (DC_Unique _ _)) _ -> True
    NIdx i
        | i >= 0 -> True
        | otherwise -> undefined
    LVar _ -> True
    _ -> False

validateGoalTerm :: TermNode -> Either TermNode ()
validateGoalTerm goal = case unfoldlNApp goal of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) -> validateGoalTerm left >> validateGoalTerm right
    (NCon (DC (DC_LO LO_or)) _, [left, right]) -> validateGoalTerm left >> validateGoalTerm right
    (NCon (DC (DC_LO LO_imply)) _, [antecedent, consequent]) ->
        validateLocalClauseTerm antecedent >> validateGoalTerm consequent
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) -> validateGoalTerm body
    (NCon (DC (DC_LO LO_sigma)) _, [NLam _ _ body _]) -> validateGoalTerm body
    (NCon (DC (DC_LO LO_true)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_fail)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_cut)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_debug)) _, [_]) -> Right ()
    (NCon (DC (DC_LO LO_is)) _, [_, _]) -> Right ()
    (NCon (DC (DC_LO _)) _, _) -> Left goal
    _ -> Right ()

type GoalAnchors = (Set.Set Int, Set.Set LogicVar)

emptyGoalAnchors :: GoalAnchors
emptyGoalAnchors = (Set.empty, Set.empty)

unionGoalAnchors :: GoalAnchors -> GoalAnchors -> GoalAnchors
unionGoalAnchors (indices1, variables1) (indices2, variables2) =
    (indices1 `Set.union` indices2, variables1 `Set.union` variables2)

underGoalBinder :: Bool -> GoalAnchors -> GoalAnchors
underGoalBinder anchorsBinder (indices, variables) =
    ( if anchorsBinder
        then Set.insert 0 shifted
        else shifted
    , variables
    )
  where
    shifted = Set.mapMonotonic (+ 1) indices

termGoalAnchors :: TermNode -> GoalAnchors
termGoalAnchors = go . rewrite NF where
    go term = case term of
        LVar variable -> (Set.empty, Set.singleton variable)
        NCon _ _ -> emptyGoalAnchors
        NIdx index
            | index >= 0 -> (Set.singleton index, Set.empty)
            | otherwise -> undefined
        NApp lhs rhs _ -> go lhs `unionGoalAnchors` go rhs
        NLam _ _ body _ -> lowerBinder (go body)
        suspended@Susp {} -> go (rewrite NF suspended)
        NPresburgerCheck _ freeOf _ ->
            foldr (unionGoalAnchors . go) emptyGoalAnchors (Map.elems freeOf)

    lowerBinder (indices, variables) =
        (Set.mapMonotonic (subtract 1) (Set.filter (> 0) indices), variables)

validateAnchoredGoal :: GoalAnchors -> TermNode -> Either TermNode ()
validateAnchoredGoal anchors goal = case unfoldlNApp goal of
    (NCon (DC (DC_LO LO_and)) _, [left, right]) ->
        validateAnchoredGoal anchors left >> validateAnchoredGoal anchors right
    (NCon (DC (DC_LO LO_or)) _, [left, right]) ->
        validateAnchoredGoal anchors left >> validateAnchoredGoal anchors right
    (NCon (DC (DC_LO LO_imply)) _, [antecedent, consequent]) ->
        validateLocalClauseTerm antecedent >> validateAnchoredGoal anchors consequent
    (NCon (DC (DC_LO LO_pi)) _, [NLam _ _ body _]) ->
        validateAnchoredGoal (underGoalBinder True anchors) body
    (NCon (DC (DC_LO LO_sigma)) _, [NLam _ _ body _]) ->
        -- A rigid `pi' parameter is directly dispatchable.  A fresh flexible
        -- `sigma' variable is not: calling it before some goal binds it would
        -- reach Runtime.dispatch as an LVar-headed goal.  Conservatively do
        -- not treat the sigma binder itself as a predicate-call anchor.
        validateAnchoredGoal (underGoalBinder False anchors) body
    (NCon (DC (DC_LO LO_true)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_fail)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_cut)) _, []) -> Right ()
    (NCon (DC (DC_LO LO_debug)) _, [_]) -> Right ()
    (NCon (DC (DC_LO LO_is)) _, [_, _]) -> Right ()
    (NCon (DC (DC_LO _)) _, _) -> Left goal
    (NIdx index, _)
        | index >= 0 && index `Set.member` fst anchors -> Right ()
        | index < 0 -> undefined
        | otherwise -> Left goal
    (LVar variable, _)
        | variable `Set.member` snd anchors -> Right ()
        | otherwise -> Left goal
    (NCon _ _, _) -> Right ()
    (NPresburgerCheck _ _ _, []) -> Right ()
    _ -> Left goal

primitivePredicateNames :: [SmallId]
primitivePredicateNames = ["print", "read"]

checkOwnFixityAgainstImports :: NotationDB -> [DeclRep] -> Either FixityError ()
checkOwnFixityAgainstImports imported = mapM_ checkDecl where
    importedFixities = Notation.declaredFixityList imported
    checkDecl (RFixityDecl loc form name prec)
        | prec < 0 || prec > 9 =
            Left (FixityError loc "Fixity precedence must be between 0 and 9.")
        | otherwise = mapM_ (checkAlias loc name fp) (Notation.fixityAliases name)
        where
            precedence = fromInteger prec
            fp = (fixityKind form, precedence)
    checkDecl _ = Right ()
    checkAlias loc name fp alias = case lookup alias importedFixities of
        Just importedFp | importedFp /= fp ->
            Left (FixityError loc ("Fixity declaration for `" ++ name ++ "' conflicts with an imported fixity."))
        _ -> Right ()
    fixityKind FF_InfixL = Notation.FK_InfixL
    fixityKind FF_InfixR = Notation.FK_InfixR
    fixityKind FF_InfixN = Notation.FK_InfixN
    fixityKind FF_Prefix = Notation.FK_Prefix

data Origins
    = Origins
        { oKinds :: !(Map.Map TypeConstructor DeclOrigin)
        , oTypes :: !(Map.Map DataConstructor DeclOrigin)
        , oFixity :: !(Map.Map SmallId DeclOrigin)
        , oAbbrev :: !(Map.Map SmallId DeclOrigin)
        , oNotation :: !(Map.Map SmallId DeclOrigin)
        }
    deriving ()

data DeclOrigin
    = DeclOrigin
        { originModuleName :: !String
        , originModulePath :: !FilePath
        }
    deriving ()

emptyOrigins :: Origins
emptyOrigins = Origins Map.empty Map.empty Map.empty Map.empty Map.empty

combineOwnImport :: Monad m => DiagnosticMode -> Maybe String -> SourceLines -> (KindEnv, TypeEnv, NotationDB, ExpansionDB, Origins) -> ((SLoc, String), ModuleEnv) -> Loader m (KindEnv, TypeEnv, NotationDB, ExpansionDB, Origins)
combineOwnImport mode moduleName sourceLines (k, t, n, e, o) ((iloc, _), env) = do
    let current = DeclOrigin (moduleEnvName env) (moduleEnvPath env)
        dependencyPaths = filter (/= moduleEnvPath env) (moduleEnvClosure env)
    (k', oK) <- liftEither (mergeKindsStrict mode moduleName sourceLines iloc current (oKinds o) k (moduleEnvOwnKinds env))
    (t', oT) <- liftEither (mergeTypesStrict mode moduleName sourceLines iloc current (oTypes o) t (moduleEnvOwnTypes env))
    oF <- liftEither (mergeFixityStrict mode moduleName sourceLines iloc current (oFixity o) n (moduleEnvOwnNotation env))
    (e', oA, oN, shadowA, shadowN) <- liftEither
        (mergeExpStrict mode moduleName sourceLines iloc current dependencyPaths
            (oAbbrev o) (oNotation o) e (moduleEnvOwnExpansion env))
    case Notation.validateExpansionDB e' of
        Left expansionError -> throwE (importExpansionCycleErr mode moduleName sourceLines iloc expansionError)
        Right () -> return ()
    let n' = Notation.mergeWithShadows shadowA shadowN n (moduleEnvOwnNotation env)
    return (k', t', n', e', Origins { oKinds = oK, oTypes = oT, oFixity = oF, oAbbrev = oA, oNotation = oN })

mergeKindsStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> DeclOrigin -> Map.Map TypeConstructor DeclOrigin -> KindEnv -> KindEnv -> Either ErrMsg (KindEnv, Map.Map TypeConstructor DeclOrigin)
mergeKindsStrict mode moduleName sourceLines iloc current origin0 old new = foldr step (Right (old, origin0)) (Map.toList new) where
    step (tc, k) acc = do
        (m, origin) <- acc
        let prior = Map.lookup tc origin
        case Map.lookup tc m of
            Nothing -> Right (Map.insert tc k m, Map.insert tc current origin)
            Just k'
                | k == k' -> Right (m, origin)
                | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C1" prior current (showTC tc) "kind" (pprint 0 k' "") (pprint 0 k ""))

mergeTypesStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> DeclOrigin -> Map.Map DataConstructor DeclOrigin -> TypeEnv -> TypeEnv -> Either ErrMsg (TypeEnv, Map.Map DataConstructor DeclOrigin)
mergeTypesStrict mode moduleName sourceLines iloc current origin0 old new = foldr step (Right (old, origin0)) (Map.toList new) where
    step (dc, p) acc = do
        (m, origin) <- acc
        let prior = Map.lookup dc origin
        case Map.lookup dc m of
            Nothing -> Right (Map.insert dc p m, Map.insert dc current origin)
            Just p'
                | polyTypeEq p p' -> Right (m, origin)
                | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C2" prior current (showDC dc) "type" "<scheme>" "<scheme>")

polyTypeEq :: PolyType -> PolyType -> Bool
polyTypeEq (Forall xs t) (Forall ys u)
    | length xs /= length ys = False
    | not (wellScopedMono (length xs) t) = False
    | not (wellScopedMono (length ys) u) = False
    | otherwise = alphaNormalizeMono t == alphaNormalizeMono u

wellScopedMono :: Int -> MonoType Int -> Bool
wellScopedMono binderCount typ = case typ of
    TyVar index -> 0 <= index && index < binderCount
    TyCon _ -> True
    TyApp left right -> wellScopedMono binderCount left && wellScopedMono binderCount right
    TyMTV _ -> True

alphaNormalizeMono :: MonoType Int -> MonoType Int
alphaNormalizeMono typ = State.evalState (go typ) (Map.empty, 0) where
    go :: MonoType Int -> State.State (Map.Map Int Int, Int) (MonoType Int)
    go (TyVar old) = do
        (renaming, next) <- State.get
        case Map.lookup old renaming of
            Just new -> return (TyVar new)
            Nothing -> do
                State.put (Map.insert old next renaming, next + 1)
                return (TyVar next)
    go (TyCon con) = return (TyCon con)
    go (TyApp left right) = TyApp <$> go left <*> go right
    go (TyMTV mtv) = return (TyMTV mtv)

showTC :: TypeConstructor -> String
showTC (TC_Named s) = s
showTC tc = show tc

showDC :: DataConstructor -> String
showDC (DC_Named s) = s
showDC dc = show dc

mergeFixityStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> DeclOrigin -> Map.Map SmallId DeclOrigin -> NotationDB -> NotationDB -> Either ErrMsg (Map.Map SmallId DeclOrigin)
mergeFixityStrict mode moduleName sourceLines iloc current origin0 old new
    = foldr step (Right origin0) (Notation.declaredFixityList new)
    where
        step (name, fp) acc = do
            origin <- acc
            let prior = Map.lookup name origin
            case lookupFixity name old of
                Nothing -> Right (Map.insert name current origin)
                Just fp'
                    | fp == fp' -> Right (Map.insertWith (\_ first -> first) name current origin)
                    | Nothing <- prior -> Right (Map.insert name current origin)
                    | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C5" prior current name "fixity" (showFixity fp') (showFixity fp))
        lookupFixity name db = lookup name (Notation.fixityList db)
        showFixity (kind, prec) = shows kind (" " ++ shows prec "")

mergeExpStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> DeclOrigin -> [FilePath] -> Map.Map SmallId DeclOrigin -> Map.Map SmallId DeclOrigin -> ExpansionDB -> ExpansionDB -> Either ErrMsg (ExpansionDB, Map.Map SmallId DeclOrigin, Map.Map SmallId DeclOrigin, [SmallId], [SmallId])
mergeExpStrict mode moduleName sourceLines iloc current dependencyPaths oA0 oN0 old new
    = do
        (oA, shadowA) <- foldr stepA (Right (oA0, [])) (Notation.declaredTypeAbbrevList new)
        (oN, shadowN) <- foldr stepN (Right (oN0, [])) (Notation.declaredTermNotationList new)
        Right (Notation.mergeExpansionWithShadows shadowA shadowN old new, oA, oN, shadowA, shadowN)
    where
        stepA (nm, ps, rhs) acc = do
            (oA, shadows) <- acc
            let prior = Map.lookup nm oA
            case lookup nm [ (n', (p', r')) | (n', p', r') <- Notation.typeAbbrevList old ] of
                Nothing -> Right (Map.insert nm current oA, shadows)
                Just (ps', rhs')
                    | typeRepAlphaEq ps rhs ps' rhs'
                    , shouldShadow prior -> Right (Map.insert nm current oA, nm : shadows)
                    | typeRepAlphaEq ps rhs ps' rhs' -> Right (oA, shadows)
                    | shouldShadow prior -> Right (Map.insert nm current oA, nm : shadows)
                    | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C3" prior current nm "abbreviation" "<prior body>" "<current body>")
        stepN (nm, ps, rhs) acc = do
            (oN, shadows) <- acc
            let prior = Map.lookup nm oN
            case lookup nm [ (n', (p', r')) | (n', p', r') <- Notation.termNotationList old ] of
                Nothing -> Right (Map.insert nm current oN, shadows)
                Just (ps', rhs')
                    | termRepAlphaEq ps rhs ps' rhs'
                    , shouldShadow prior -> Right (Map.insert nm current oN, nm : shadows)
                    | termRepAlphaEq ps rhs ps' rhs' -> Right (oN, shadows)
                    | shouldShadow prior -> Right (Map.insert nm current oN, nm : shadows)
                    | otherwise -> Left
                        (inconsErr2 mode moduleName sourceLines iloc "C4" prior current nm "notation"
                            "<prior body>" "<current body>")
        shouldShadow Nothing = True
        shouldShadow (Just prior) = originModulePath prior `elem` dependencyPaths

importExpansionCycleErr :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> Notation.ExpansionError -> ErrMsg
importExpansionCycleErr mode moduleName sourceLines importLoc expansionError =
    moduleErr mode moduleName sourceLines importLoc message
    where
        message = case expansionError of
            Notation.TypeExpansionCycle _ names ->
                "Import composition creates a cyclic type abbreviation: "
                    ++ List.intercalate " -> " names ++ "."
            Notation.TermExpansionCycle _ names ->
                "Import composition creates a cyclic term notation: "
                    ++ List.intercalate " -> " names ++ "."

inconsErr2 :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Maybe DeclOrigin -> DeclOrigin -> String -> String -> String -> String -> ErrMsg
inconsErr2 mode moduleName sourceLines iloc tag mPrior current dname kindLabel rhsA rhsB = moduleErr mode moduleName sourceLines iloc msg where
    currentLabel = renderOrigin current
    msg = case mPrior of
        Just prior -> concat
            [ "Import inconsistency (" ++ tag ++ "): `" ++ dname
            , "' is declared by both " ++ renderOrigin prior ++ " and " ++ currentLabel
            , " with disagreeing " ++ kindLabel ++ ". "
            , "(" ++ renderOrigin prior ++ ": " ++ rhsA ++ "; " ++ currentLabel ++ ": " ++ rhsB ++ ".)"
            ]
        Nothing -> concat
            [ "Import inconsistency (" ++ tag ++ "): `" ++ dname
            , "' is declared by " ++ currentLabel ++ " with a different "
            , kindLabel ++ " than the built-in seed."
            ]

-- A path-derived display name is not injective: for example, `a/b.hol' and
-- `a.b.hol' both display as `a.b'.  Diagnostics therefore include canonical
-- identity as well as the convenient display name.
renderOrigin :: DeclOrigin -> String
renderOrigin origin = "`" ++ originModuleName origin ++ "' (" ++ originModulePath origin ++ ")"

typeRepAlphaEq :: [LargeId] -> TypeRep -> [LargeId] -> TypeRep -> Bool
typeRepAlphaEq leftParams left rightParams right
    | length leftParams /= length rightParams = False
    | otherwise = go left right
    where
        go (RTyPrn _ a) b = go a b
        go a (RTyPrn _ b) = go a b
        go (RTyVar _ x) (RTyVar _ y) = alphaNameEq leftParams x rightParams y
        go (RTyCon _ x) (RTyCon _ y) = x == y
        go (RTyApp _ a b) (RTyApp _ c d) = go a c && go b d
        go _ _ = False

alphaNameEq :: [LargeId] -> LargeId -> [LargeId] -> LargeId -> Bool
alphaNameEq leftParams left rightParams right =
    case (List.elemIndex left leftParams, List.elemIndex right rightParams) of
        (Just i, Just j) -> i == j
        (Nothing, Nothing) -> left == right
        _ -> False

termRepAlphaEq :: [LargeId] -> TermRep -> [LargeId] -> TermRep -> Bool
termRepAlphaEq leftParams = go [] where
    go leftBound left rightParams right = compareTerm leftBound left [] right
      where
        compareTerm lb (RPrn _ a) rb b = compareTerm lb a rb b
        compareTerm lb a rb (RPrn _ b) = compareTerm lb a rb b
        compareTerm lb (RVar _ x) rb (RVar _ y) = variableEq lb x rb y
        compareTerm lb (RCon _ (DC_Named x)) rb (RCon _ (DC_Named y)) =
            namedConstantEq lb x rb y
        compareTerm lb (RVar _ x) rb (RCon _ (DC_Named y)) = boundOccurrenceEq lb x rb y
        compareTerm lb (RCon _ (DC_Named x)) rb (RVar _ y) = boundOccurrenceEq lb x rb y
        compareTerm _ (RCon _ x) _ (RCon _ y) = x == y
        compareTerm lb (RApp _ a b) rb (RApp _ c d) = compareTerm lb a rb c && compareTerm lb b rb d
        compareTerm lb (RAbs _ x a) rb (RAbs _ y b) = compareTerm (x : lb) a (y : rb) b
        compareTerm _ (R_wc _) _ (R_wc _) = True
        compareTerm _ _ _ _ = False
        variableEq lb x rb y = case (List.elemIndex x lb, List.elemIndex y rb) of
            (Just i, Just j) -> i == j
            (Nothing, Nothing) -> alphaNameEq leftParams x rightParams y
            _ -> False
        namedConstantEq lb x rb y = case (List.elemIndex x lb, List.elemIndex y rb) of
            (Just i, Just j) -> i == j
            (Nothing, Nothing) -> x == y
            _ -> False
        boundOccurrenceEq lb x rb y = case (List.elemIndex x lb, List.elemIndex y rb) of
            (Just i, Just j) -> i == j
            _ -> False

extractHeaderAndImports :: DiagnosticMode -> Maybe String -> SourceLines -> [DeclRep] -> Either ErrMsg (Maybe (SLoc, String), [(SLoc, String)], [DeclRep])
extractHeaderAndImports mode moduleName sourceLines decls0
    = case decls0 of
        RModuleHeaderDecl loc n : rest -> do
            validateModuleName "module name" loc n
            (imps, body) <- partitionImports rest
            return (Just (loc, n), imps, body)
        rest -> do
            (imps, body) <- partitionImports rest
            return (Nothing, imps, body)
    where
        partitionImports (RImportDecl loc n : rest) = do
            validateModuleName "module locator" loc n
            (imps, body) <- partitionImports rest
            return ((loc, n) : imps, body)
        partitionImports rest =
            case [ loc | RImportDecl loc _ <- rest ] of
                (loc : _) -> Left (moduleErr mode moduleName sourceLines loc "`import' declarations must precede all other declarations.")
                [] -> case [ loc | RModuleHeaderDecl loc _ <- rest ] of
                    (loc : _) -> Left (moduleErr mode moduleName sourceLines loc "`module' header must be the first declaration of the file.")
                    [] -> return ([], rest)
        validateModuleName label loc name
            | validModuleName name = Right ()
            | otherwise = Left (moduleErr mode moduleName sourceLines loc
                ("Invalid " ++ label ++ " `" ++ name ++ "'. Use one or more dot-separated ASCII identifier segments; filesystem path separators and symbolic identifiers are not module locators."))

validModuleName :: String -> Bool
validModuleName name = not (null segments) && all validSegment segments where
    segments = splitOn '.' name
    validSegment [] = False
    validSegment (first : rest) = isAsciiLetter first && all isAsciiAlphaNumUnderscore rest
    isAsciiLetter ch = ('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z')
    isAsciiAlphaNumUnderscore ch = isAsciiLetter ch || ('0' <= ch && ch <= '9') || ch == '_'

liftEither :: Monad m => Either ErrMsg a -> Loader m a
liftEither = either throwE return
