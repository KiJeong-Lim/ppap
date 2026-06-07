module Hol.BETA.ModuleLoader
    ( ModuleEnv (..)
    , LoadedModule (..)
    , loadMain
    , loadMainWithDiagnostic
    , pathDerivedName
    ) where

import Hol.BETA.Arith (installPresburger)
import Hol.BETA.Compiler (convertProgram)
import Hol.BETA.Desugarer (desugarProgramWithModule)
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.FixityResolver (FixityError (..), resolveDeclsWithFixity)
import Hol.BETA.Notation (NotationDB, ExpansionDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.PlanHolLexer
import Hol.BETA.PlanHolParser (runHolParser)
import Hol.BETA.TermNode (TermNode)
import Hol.BETA.TypeChecker (checkTypeWithModule)

import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.List as List
import qualified Z.Doc
import System.Directory (canonicalizePath, doesFileExist, getCurrentDirectory)
import System.FilePath ((</>))
import Z.System.File (readFileNow)
import Z.Utils

data ModuleEnv
    = ModuleEnv
    { moduleEnvName :: String
    , moduleEnvPath :: FilePath
    , moduleEnvKinds :: KindEnv
    , moduleEnvTypes :: TypeEnv
    , moduleEnvFacts :: [TermNode]
    , moduleEnvNotation :: NotationDB
    , moduleEnvExpansion :: ExpansionDB
    , moduleEnvImports :: [String]
    , moduleEnvWarnings :: [ErrMsg]
    } deriving ()

data LoadedModule
    = LoadedModule
    { loadedMain :: ModuleEnv
    , loadedAll :: Map String ModuleEnv
    , loadedOrder :: [String]
    , loadedWarnings :: [ErrMsg]
    } deriving ()

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

type Loader m a = ExceptT ErrMsg (State.StateT LoaderState m) a

moduleErr :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> ErrMsg
moduleErr mode moduleName sourceLines loc msg = diagnosticWithModule mode "HolBETA-ModuleError" moduleName sourceLines loc [Z.Doc.text msg]

moduleWarning :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> ErrMsg
moduleWarning mode moduleName sourceLines loc msg = diagnosticWarningWithModule mode "HolBETA-ModuleWarning" moduleName sourceLines loc [Z.Doc.text msg]

pathDerivedName :: FilePath -> FilePath -> String
pathDerivedName root absPath = map dotSep stripped where
    rel = makeRel root absPath
    stripped = dropDotHol rel
    dotSep '/' = '.'
    dotSep c   = c
    dropDotHol p
        | List.isSuffixOf ".hol" p = take (length p - 4) p
        | otherwise                = p
    makeRel base path
        | List.isPrefixOf (base ++ "/") path = drop (length base + 1) path
        | base == path = path
        | otherwise = path

loadMain :: UniqueM m => KindEnv -> TypeEnv -> [TermNode] -> FilePath -> m (Either ErrMsg LoadedModule)
loadMain = loadMainWithDiagnostic DiagnosticPretty

loadMainWithDiagnostic :: UniqueM m => DiagnosticMode -> KindEnv -> TypeEnv -> [TermNode] -> FilePath -> m (Either ErrMsg LoadedModule)
loadMainWithDiagnostic mode initialKinds initialTypes initialFacts mainPath = do
    root <- liftIO getCurrentDirectory
    rootC <- liftIO (canonicalizePath root)
    canonicalMain <- liftIO (canonicalizePath mainPath)
    let st0 = LoaderState
            { lsLoaded = Map.empty, lsLoading = [], lsOrder = [], lsRoot = rootC
            , lsInitialKinds = initialKinds
            , lsInitialTypes = initialTypes
            , lsInitialFacts = initialFacts
            , lsDiagnosticMode = mode
            , lsWarnings = []
            }
    (eMain, stN) <- State.runStateT (runExceptT (loadFile canonicalMain Nothing)) st0
    case eMain of
        Left err -> return (Left err)
        Right env -> return (Right (LoadedModule { loadedMain  = env , loadedAll   = Map.fromList [ (moduleEnvName e, e) | e <- Map.elems (lsLoaded stN) ] , loadedOrder = reverse (lsOrder stN) , loadedWarnings = reverse (lsWarnings stN) }))

loadFile :: UniqueM m => FilePath -> Maybe (FilePath, SLoc, SourceLines) -> Loader m ModuleEnv
loadFile canonicalPath importContext = do
    st <- lift State.get
    let mode = lsDiagnosticMode st
    case Map.lookup canonicalPath (lsLoaded st) of
        Just env -> return env
        Nothing -> do
            let mname = pathDerivedName (lsRoot st) canonicalPath
            case List.lookup mname (lsLoading st) of
                Just _ -> do
                    let cycle = reverse (mname : map fst (takeWhile ((/= mname) . fst) (lsLoading st)))
                        chain = List.intercalate " -> " (cycle ++ [mname])
                    throwE $ case importContext of
                        Just (importerPath, loc, sourceLines) -> moduleErr mode (Just importerPath) sourceLines loc ("Import cycle detected: " ++ chain ++ ".")
                        Nothing -> diagnosticNoLocWith mode "HolBETA-ModuleError" [Z.Doc.text ("Import cycle detected: " ++ chain ++ ".")]
                Nothing -> do
                    msrc <- liftIO (readFileNow canonicalPath)
                    case msrc of
                        Nothing -> throwE (diagnosticNoLocWith mode "HolBETA-FileError" [Z.Doc.text ("Cannot read file `" ++ canonicalPath ++ "'.")])
                        Just src -> do
                            let sourceLines = Just (lines src)
                            case runHolLexer src of
                                Left (row, col) -> throwE (diagnosticWithModule mode "HolBETA-LexError" (Just canonicalPath) sourceLines (SLoc (row, col) (row, col)) [Z.Doc.text ("Lexing failed in `" ++ canonicalPath ++ "'.")])
                                Right tokens -> case runHolParser tokens of
                                    Left Nothing -> throwE (diagnosticNoLocWith mode "HolBETA-ParseError" [Z.Doc.text ("Parsing failed at EOF in `" ++ canonicalPath ++ "'.")])
                                    Left (Just token) -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) sourceLines (getSLoc token) [Z.Doc.text ("Parsing failed in `" ++ canonicalPath ++ "'.")])
                                    Right (Left _) -> throwE (diagnosticNoLocWith mode "HolBETA-ParseError" [Z.Doc.text ("File `" ++ canonicalPath ++ "' is a query, not a program.")])
                                    Right (Right decls0) -> case extractHeaderAndImports mode (Just canonicalPath) sourceLines decls0 of
                                        Left err -> throwE err
                                        Right (mHeader, imports, body0) -> elaborate canonicalPath mname (lines src) mHeader imports body0

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
            env <- loadImport mname canonicalPath (Just sourceLines) imp
            return (imp, env)
    lift (State.modify (\s -> s { lsWarnings = reverse importWarnings ++ lsWarnings s }))
    lift (State.modify (\s -> s { lsLoading = (mname, canonicalPath) : lsLoading s }))
    importedEnvsWithLocs <- mapM go importsUnique
    lift (State.modify (\ s -> s { lsLoading = drop 1 (lsLoading s) }))
    st <- lift State.get
    let initialKinds = lsInitialKinds st
        initialFacts = lsInitialFacts st
        initialTypes = lsInitialTypes st
    (composedKinds, composedTypes, composedNotation, composedExpansion, _origins) <- foldM (combineImport mode (Just canonicalPath) (Just sourceLines)) (initialKinds, initialTypes, Notation.initial, Notation.initialExpansionDB, emptyOrigins) importedEnvsWithLocs
    let importedFacts = concatMap (drop (length initialFacts) . moduleEnvFacts . snd) importedEnvsWithLocs
    body <- case resolveDeclsWithFixity composedNotation body0 of
        Left (FixityError loc msg) -> throwE (diagnosticWithModule mode "HolBETA-ParseError" (Just canonicalPath) (Just sourceLines) loc [Z.Doc.text ("Parsing failed in `" ++ canonicalPath ++ "'."), Z.Doc.text msg])
        Right decls -> return decls
    (env1, ownNotation0, ownExpansion0) <- desugarProgramWithModule mode (Just canonicalPath) (Just sourceLines) composedKinds composedTypes mname body
    let ownNotation  = mergeNotation composedNotation ownNotation0
        ownExpansion = mergeExpansion composedExpansion ownExpansion0
    facts2 <- sequence [ checkTypeWithModule mode (Just canonicalPath) (Just sourceLines) ownNotation (_TypeDecls env1) fact mkTyO | fact <- _FactDecls env1 ]
    facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
    ownFactsR <- sequence [ either throwE return (installPresburger f) | f <- facts3 ]
    let env = ModuleEnv
            { moduleEnvName = mname
            , moduleEnvPath = canonicalPath
            , moduleEnvKinds = _KindDecls env1
            , moduleEnvTypes = _TypeDecls env1
            , moduleEnvFacts = initialFacts ++ importedFacts ++ ownFactsR
            , moduleEnvNotation = ownNotation
            , moduleEnvExpansion = ownExpansion
            , moduleEnvImports = [ m | (_, m) <- importsUnique ]
            , moduleEnvWarnings = importWarnings
            }
    lift (State.modify (\s -> s { lsLoaded = Map.insert canonicalPath env (lsLoaded s), lsOrder  = mname : lsOrder s }))
    return env

loadImport :: UniqueM m => String -> FilePath -> SourceLines -> (SLoc, String) -> Loader m ModuleEnv
loadImport importerName importerPath sourceLines (importLoc, importedName) = do
    st <- lift State.get
    let dir = takeDir importerPath
        root = lsRoot st
    mFound <- liftIO (resolveImport dir root importedName)
    case mFound of
        Nothing -> do
            st <- lift State.get
            throwE (moduleErr (lsDiagnosticMode st) (Just importerPath) sourceLines importLoc ("Cannot resolve module `" ++ importedName ++ "' from `" ++ importerPath ++ "'."))
        Just canonical -> loadFile canonical (Just (importerPath, importLoc, sourceLines))

takeDir :: FilePath -> FilePath
takeDir p = case break (\c -> c == '/') (reverse p) of
    (_, '/' : rest) -> reverse rest
    _ -> "."

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

duplicateImportWarnings :: DiagnosticMode -> String -> SourceLines -> [(SLoc, String)] -> [ErrMsg]
duplicateImportWarnings mode moduleName sourceLines = go [] where
    go _ [] = []
    go seen ((loc, name) : rest) = if name `elem` seen then moduleWarning mode (Just moduleName) sourceLines loc ("Duplicate import `" ++ name ++ "' ignored.") : go seen rest else go (name : seen) rest

mergeNotation :: NotationDB -> NotationDB -> NotationDB
mergeNotation = Notation.merge

mergeExpansion :: ExpansionDB -> ExpansionDB -> ExpansionDB
mergeExpansion = Notation.mergeExpansion

data Origins
    = Origins
    { oKinds :: !(Map.Map TypeConstructor String)
    , oTypes :: !(Map.Map DataConstructor String)
    , oFixity :: !(Map.Map SmallId String)
    , oAbbrev :: !(Map.Map SmallId String)
    , oNotation :: !(Map.Map SmallId String)
    } deriving ()

emptyOrigins :: Origins
emptyOrigins = Origins Map.empty Map.empty Map.empty Map.empty Map.empty

combineImport :: Monad m => DiagnosticMode -> Maybe String -> SourceLines -> (KindEnv, TypeEnv, NotationDB, ExpansionDB, Origins) -> ((SLoc, String), ModuleEnv) -> Loader m (KindEnv, TypeEnv, NotationDB, ExpansionDB, Origins)
combineImport mode moduleName sourceLines (k, t, n, e, o) ((iloc, iname), env) = do
    (k', oK) <- liftEither (mergeKindsStrict   mode moduleName sourceLines iloc iname (oKinds o) k (moduleEnvKinds env))
    (t', oT) <- liftEither (mergeTypesStrict   mode moduleName sourceLines iloc iname (oTypes o) t (moduleEnvTypes env))
    (n', oF) <- liftEither (mergeFixityStrict  mode moduleName sourceLines iloc iname (oFixity o) n (moduleEnvNotation env))
    (e', oA, oN) <- liftEither (mergeExpStrict mode moduleName sourceLines iloc iname (oAbbrev o) (oNotation o) e (moduleEnvExpansion env))
    return (k', t', n', e', Origins { oKinds = oK, oTypes = oT, oFixity = oF, oAbbrev = oA, oNotation = oN })

mergeKindsStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Map.Map TypeConstructor String -> KindEnv -> KindEnv -> Either ErrMsg (KindEnv, Map.Map TypeConstructor String)
mergeKindsStrict mode moduleName sourceLines iloc iname origin0 old new = foldr step (Right (old, origin0)) (Map.toList new) where
    step (tc, k) acc = do
        (m, origin) <- acc
        let prior = Map.lookup tc origin
        case Map.lookup tc m of
            Nothing -> Right (Map.insert tc k m, Map.insert tc iname origin)
            Just k'
                | k == k' -> Right (m, origin)
                | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C1" prior iname (showTC tc) "kind" (pprint 0 k' "") (pprint 0 k ""))

mergeTypesStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Map.Map DataConstructor String -> TypeEnv -> TypeEnv -> Either ErrMsg (TypeEnv, Map.Map DataConstructor String)
mergeTypesStrict mode moduleName sourceLines iloc iname origin0 old new = foldr step (Right (old, origin0)) (Map.toList new) where
    step (dc, p) acc = do
        (m, origin) <- acc
        let prior = Map.lookup dc origin
        case Map.lookup dc m of
            Nothing -> Right (Map.insert dc p m, Map.insert dc iname origin)
            Just p'
                | polyTypeEq p p' -> Right (m, origin)
                | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C2" prior iname (showDC dc) "type" "<scheme>" "<scheme>")

polyTypeEq :: PolyType -> PolyType -> Bool
polyTypeEq (Forall xs t) (Forall ys u)
    | length xs /= length ys = False
    | otherwise              = t == u

showTC :: TypeConstructor -> String
showTC (TC_Named s) = s
showTC tc = show tc

showDC :: DataConstructor -> String
showDC (DC_Named s) = s
showDC dc = show dc

mergeFixityStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Map.Map SmallId String -> NotationDB -> NotationDB -> Either ErrMsg (NotationDB, Map.Map SmallId String)
mergeFixityStrict mode moduleName sourceLines iloc iname origin0 old new
    = do
        origin' <- foldr step (Right origin0) (nonSeedFixities new)
        Right (Notation.merge old new, origin')
    where
        nonSeedFixities db =
            [ (name, fp)
            | (name, fp) <- Notation.fixityList db
            , lookup name (Notation.fixityList Notation.initial) /= Just fp
            ]
        step (name, fp) acc = do
            origin <- acc
            let prior = Map.lookup name origin
            case lookupFixity name old of
                Nothing -> Right (Map.insert name iname origin)
                Just fp'
                    | fp == fp' -> Right (Map.insert name iname origin)
                    | Nothing <- prior -> Right (Map.insert name iname origin)
                    | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C5" prior iname name "fixity" (showFixity fp') (showFixity fp))
        lookupFixity name db = lookup name (Notation.fixityList db)
        showFixity (kind, prec) = shows kind (" " ++ shows prec "")

mergeExpStrict :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Map.Map SmallId String -> Map.Map SmallId String -> ExpansionDB -> ExpansionDB -> Either ErrMsg (ExpansionDB, Map.Map SmallId String, Map.Map SmallId String)
mergeExpStrict mode moduleName sourceLines iloc iname oA0 oN0 old new
    = do
        oA <- foldr stepA (Right oA0) (Notation.typeAbbrevList new)
        oN <- foldr stepN (Right oN0) (Notation.termNotationList new)
        Right (Notation.mergeExpansion old new, oA, oN)
    where
        stepA (nm, ps, rhs) acc = do
            oA <- acc
            let prior = Map.lookup nm oA
            case lookup nm [ (n', (p', r')) | (n', p', r') <- Notation.typeAbbrevList old ] of
                Nothing -> Right (Map.insert nm iname oA)
                Just (ps', rhs')
                    | ps == ps' && typeRepEq rhs rhs' -> Right oA
                    | otherwise -> Left (inconsErr2 mode moduleName sourceLines iloc "C3" prior iname nm "abbreviation" "<prior body>" "<current body>")
        stepN (nm, ps, rhs) acc = do
            oN <- acc
            let prior = Map.lookup nm oN
            case lookup nm [ (n', (p', r')) | (n', p', r') <- Notation.termNotationList old ] of
                Nothing -> Right (Map.insert nm iname oN)
                Just (ps', rhs')
                    | ps == ps' && termRepEq rhs rhs' -> Right oN
                    | otherwise -> Left
                        (inconsErr2 mode moduleName sourceLines iloc "C4" prior iname nm "notation"
                            "<prior body>" "<current body>")

inconsErr2 :: DiagnosticMode -> Maybe String -> SourceLines -> SLoc -> String -> Maybe String -> String -> String -> String -> String -> String -> ErrMsg
inconsErr2 mode moduleName sourceLines iloc tag mPrior iname dname kindLabel rhsA rhsB = moduleErr mode moduleName sourceLines iloc msg where
    msg = case mPrior of
        Just prior -> concat
            [ "Import inconsistency (" ++ tag ++ "): `" ++ dname
            , "' is declared by both `" ++ prior ++ "' and `" ++ iname
            , "' with disagreeing " ++ kindLabel ++ ". "
            , "(`" ++ prior ++ "': " ++ rhsA ++ "; `" ++ iname ++ "': " ++ rhsB ++ ".)"
            ]
        Nothing -> concat
            [ "Import inconsistency (" ++ tag ++ "): `" ++ dname
            , "' is declared by `" ++ iname ++ "' with a different "
            , kindLabel ++ " than the built-in seed."
            ]

typeRepEq :: TypeRep -> TypeRep -> Bool
typeRepEq (RTyPrn _ a) b = typeRepEq a b
typeRepEq a (RTyPrn _ b) = typeRepEq a b
typeRepEq (RTyVar _ x) (RTyVar _ y) = x == y
typeRepEq (RTyCon _ x) (RTyCon _ y) = x == y
typeRepEq (RTyApp _ a b) (RTyApp _ c d) = typeRepEq a c && typeRepEq b d
typeRepEq _ _ = False

termRepEq :: TermRep -> TermRep -> Bool
termRepEq (RPrn _ a) b = termRepEq a b
termRepEq a (RPrn _ b) = termRepEq a b
termRepEq (RVar _ x) (RVar _ y) = x == y
termRepEq (RCon _ x) (RCon _ y) = x == y
termRepEq (RApp _ a b) (RApp _ c d) = termRepEq a c && termRepEq b d
termRepEq (RAbs _ x a) (RAbs _ y b) = x == y && termRepEq a b
termRepEq (R_wc _) (R_wc _) = True
termRepEq _ _ = False

extractHeaderAndImports :: DiagnosticMode -> Maybe String -> SourceLines -> [DeclRep] -> Either ErrMsg (Maybe (SLoc, String), [(SLoc, String)], [DeclRep])
extractHeaderAndImports mode moduleName sourceLines decls0
    = case decls0 of
        RModuleHeaderDecl loc n : rest -> do
            (imps, body) <- partitionImports rest
            return (Just (loc, n), imps, body)
        rest -> do
            (imps, body) <- partitionImports rest
            return (Nothing, imps, body)
    where
        partitionImports (RImportDecl loc n : rest) = do
            (imps, body) <- partitionImports rest
            return ((loc, n) : imps, body)
        partitionImports rest =
            case [ loc | RImportDecl loc _ <- rest ] of
                (loc : _) -> Left (moduleErr mode moduleName sourceLines loc "`import' declarations must precede all other declarations.")
                [] -> case [ loc | RModuleHeaderDecl loc _ <- rest ] of
                    (loc : _) -> Left (moduleErr mode moduleName sourceLines loc "`module' header must be the first declaration of the file.")
                    [] -> return ([], rest)

liftEither :: Monad m => Either ErrMsg a -> Loader m a
liftEither = either throwE return
