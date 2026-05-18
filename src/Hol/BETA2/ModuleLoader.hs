-- §4.2: the BETA2 module loader.  Implements the topological load of §2.2,
-- the import composition of §2.3, and (in a follow-up step) the consistency
-- rules of §2.4.  This module has no BETA1 counterpart.
module Hol.BETA2.ModuleLoader
    ( ModuleEnv (..)
    , LoadedModule (..)
    , loadMain
    , pathDerivedName
    ) where

import Hol.BETA2.Arith (installPresburger)
import Hol.BETA2.Compiler (convertProgram)
import Hol.BETA2.Desugarer (desugarProgram)
import Hol.BETA2.Header
import Hol.BETA2.Notation (NotationDB, ExpansionDB)
import qualified Hol.BETA2.Notation as Notation
import Hol.BETA2.PlanHolLexer
import Hol.BETA2.PlanHolParser (runHolParser)
import Hol.BETA2.TermNode (TermNode)
import Hol.BETA2.TypeChecker (checkType)

import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.List as List
import System.Directory (canonicalizePath, doesFileExist, getCurrentDirectory)
import System.FilePath ((</>))
import Z.Utils

data ModuleEnv = ModuleEnv
    { moduleEnvName       :: String
    , moduleEnvPath       :: FilePath
    , moduleEnvKinds      :: KindEnv
    , moduleEnvTypes      :: TypeEnv
    , moduleEnvFacts      :: [TermNode]
    , moduleEnvNotation   :: NotationDB
    , moduleEnvExpansion  :: ExpansionDB
    , moduleEnvImports    :: [String]
    } deriving ()

data LoadedModule = LoadedModule
    { loadedMain   :: ModuleEnv
    , loadedAll    :: Map String ModuleEnv
    , loadedOrder  :: [String]
    } deriving ()

data LoaderState = LoaderState
    { lsLoaded         :: Map FilePath ModuleEnv
    , lsLoading        :: [(String, FilePath)]
    , lsOrder          :: [String]
    , lsRoot           :: FilePath
    , lsInitialKinds   :: KindEnv
    , lsInitialTypes   :: TypeEnv
    , lsInitialFacts   :: [TermNode]
    }

type Loader a = ExceptT ErrMsg (State.StateT LoaderState (UniqueT IO)) a

-- Turn `Example/foo/bar.hol` into `Example.foo.bar`.  We strip the trailing
-- `.hol`, replace `/` with `.`, and use the path *relative to the project
-- root* (i.e., the working directory at REPL launch) so that diamonds
-- through different relative paths still collapse onto one module name.
pathDerivedName :: FilePath -> FilePath -> String
pathDerivedName root absPath =
    let rel = makeRel root absPath
        stripped = dropDotHol rel
    in map dotSep stripped
  where
    dotSep '/' = '.'
    dotSep c   = c
    dropDotHol p
        | List.isSuffixOf ".hol" p = take (length p - 4) p
        | otherwise                = p
    makeRel base path
        | List.isPrefixOf (base ++ "/") path = drop (length base + 1) path
        | base == path = path
        | otherwise = path

loadMain
    :: KindEnv -> TypeEnv -> [TermNode] -> FilePath
    -> UniqueT IO (Either ErrMsg LoadedModule)
loadMain initialKinds initialTypes initialFacts mainPath = do
    root <- liftIO getCurrentDirectory
    rootC <- liftIO (canonicalizePath root)
    canonicalMain <- liftIO (canonicalizePath mainPath)
    let st0 = LoaderState
            { lsLoaded = Map.empty, lsLoading = [], lsOrder = [], lsRoot = rootC
            , lsInitialKinds = initialKinds
            , lsInitialTypes = initialTypes
            , lsInitialFacts = initialFacts
            }
    (eMain, stN) <- State.runStateT
        (runExceptT (loadFile canonicalMain Nothing))
        st0
    return $ case eMain of
        Left err -> Left err
        Right env -> Right LoadedModule
            { loadedMain  = env
            , loadedAll   = Map.fromList [ (moduleEnvName e, e) | e <- Map.elems (lsLoaded stN) ]
            , loadedOrder = reverse (lsOrder stN)
            }

-- Load (or fetch from cache) the file at `canonicalPath`.  `importSLoc`
-- is the location of the surface `import` that requested this file (used
-- for cycle-error attribution); `Nothing` means this is the main file.
loadFile :: FilePath -> Maybe SLoc -> Loader ModuleEnv
loadFile canonicalPath importSLoc = do
    st <- lift State.get
    case Map.lookup canonicalPath (lsLoaded st) of
        Just env -> return env
        Nothing -> do
            let mname = pathDerivedName (lsRoot st) canonicalPath
            case List.lookup mname (map (\ (n, p) -> (n, p)) (lsLoading st)) of
                Just _ -> do
                    let cycle = reverse (mname : map fst (takeWhile ((/= mname) . fst) (lsLoading st)))
                        chain = List.intercalate " -> " (cycle ++ [mname])
                        locStr = case importSLoc of
                            Just l -> pprint 0 l ""
                            Nothing -> "?:?"
                    throwE ("*** module-error[" ++ locStr ++ "]:\n  ? import cycle detected: " ++ chain ++ ".")
                Nothing -> do
                    src <- liftIO (readFile canonicalPath)
                    case runHolLexer src of
                        Left (row, col) -> throwE ("*** lexing-error in `" ++ canonicalPath ++ "` at row=" ++ show row ++ ", col=" ++ show col)
                        Right tokens -> case runHolParser tokens of
                            Left _ -> throwE ("*** parsing-error in `" ++ canonicalPath ++ "`.")
                            Right (Left _) -> throwE ("*** parsing-error in `" ++ canonicalPath ++ "`: file is a query, not a program.")
                            Right (Right decls) -> elaborate canonicalPath mname decls

-- Split decls into (optional header, imports, body), enforce header/import
-- ordering, recursively load each import, compose the dependency envs,
-- desugar + type-check the body against the composed env, store the
-- resulting ModuleEnv into the loader's table.
elaborate :: FilePath -> String -> [DeclRep] -> Loader ModuleEnv
elaborate canonicalPath mname decls = do
    (mHeader, imports, body) <- liftEither (extractHeaderAndImports decls)
    case mHeader of
        Just (loc, declared) | declared /= mname ->
            throwE ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? module header `" ++ declared ++ "' does not match file path-derived name `" ++ mname ++ "'.")
        _ -> return ()
    lift (State.modify (\ s -> s { lsLoading = (mname, canonicalPath) : lsLoading s }))
    importedEnvsWithLocs <- mapM
        (\imp@(_, _) -> do { env <- loadImport canonicalPath imp; return (imp, env) })
        imports
    lift (State.modify (\ s -> s { lsLoading = drop 1 (lsLoading s) }))
    st <- lift State.get
    let initialKinds = lsInitialKinds st
        initialFacts = lsInitialFacts st
        initialTypes = lsInitialTypes st
    (composedKinds, composedTypes, composedNotation, composedExpansion) <- foldM combineImport
        (initialKinds, initialTypes, Notation.initial, Notation.initialExpansionDB)
        importedEnvsWithLocs
    let importedFacts = concatMap (drop (length initialFacts) . moduleEnvFacts . snd) importedEnvsWithLocs
    (env1, ownNotation0, ownExpansion0) <- desugarProgram composedKinds composedTypes mname body
    let ownNotation  = mergeNotation composedNotation ownNotation0
        ownExpansion = mergeExpansion composedExpansion ownExpansion0
    facts2 <- sequence [ checkType ownNotation (_TypeDecls env1) fact mkTyO | fact <- _FactDecls env1 ]
    facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
    ownFactsR <- sequence [ either throwE return (installPresburger f) | f <- facts3 ]
    let env = ModuleEnv
            { moduleEnvName      = mname
            , moduleEnvPath      = canonicalPath
            , moduleEnvKinds     = _KindDecls env1
            , moduleEnvTypes     = _TypeDecls env1
            , moduleEnvFacts     = initialFacts ++ importedFacts ++ ownFactsR
            , moduleEnvNotation  = ownNotation
            , moduleEnvExpansion = ownExpansion
            , moduleEnvImports   = [ m | (_, m) <- imports ]
            }
    lift (State.modify (\ s -> s
        { lsLoaded = Map.insert canonicalPath env (lsLoaded s)
        , lsOrder  = mname : lsOrder s
        }))
    return env

loadImport :: FilePath -> (SLoc, String) -> Loader ModuleEnv
loadImport importerPath (importLoc, importedName) = do
    st <- lift State.get
    let dir = takeDir importerPath
        root = lsRoot st
    mFound <- liftIO (resolveImport dir root importedName)
    case mFound of
        Nothing -> throwE ("*** module-error[" ++ pprint 0 importLoc "]:\n  ? cannot resolve module `" ++ importedName ++ "' from `" ++ importerPath ++ "'.")
        Just canonical -> loadFile canonical (Just importLoc)

takeDir :: FilePath -> FilePath
takeDir p = case break (== '/') (reverse p) of
    (_, '/' : rest) -> reverse rest
    _ -> "."

resolveImport :: FilePath -> FilePath -> String -> IO (Maybe FilePath)
resolveImport dir root mname = do
    let rel = foldr (</>) (last segs ++ ".hol") (init segs)
          where segs = splitOn '.' mname
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

-- §2.3 composition: kinds/types use Map.union (left-biased, but imports
-- agreeing on a name will collide on identical RHSs — §2.4 will reject
-- disagreement as inconsistency; for the time being, last writer wins).
-- Notations / expansions merge component-wise, again last-writer-wins
-- pending §2.4.
mergeNotation :: NotationDB -> NotationDB -> NotationDB
mergeNotation = Notation.merge

mergeExpansion :: ExpansionDB -> ExpansionDB -> ExpansionDB
mergeExpansion = Notation.mergeExpansion

-- §2.4 consistency checks.  `combineImport (k, t, n, e) ((iloc, iname), env)`
-- merges `env` into the accumulator and fails with a §2.4 C1-C5 error
-- attributed to `iloc` if any decl in `env` disagrees with the
-- accumulator's previous content.
combineImport
    :: (KindEnv, TypeEnv, NotationDB, ExpansionDB)
    -> ((SLoc, String), ModuleEnv)
    -> Loader (KindEnv, TypeEnv, NotationDB, ExpansionDB)
combineImport (k, t, n, e) ((iloc, iname), env) = do
    k' <- liftEither (mergeKindsStrict   iloc iname k (moduleEnvKinds     env))
    t' <- liftEither (mergeTypesStrict   iloc iname t (moduleEnvTypes     env))
    n' <- liftEither (mergeFixityStrict  iloc iname n (moduleEnvNotation  env))
    e' <- liftEither (mergeExpStrict     iloc iname e (moduleEnvExpansion env))
    return (k', t', n', e')

mergeKindsStrict :: SLoc -> String -> KindEnv -> KindEnv -> Either ErrMsg KindEnv
mergeKindsStrict iloc iname old new = foldr step (Right old) (Map.toList new)
  where
    step (tc, k) acc = do
        m <- acc
        case Map.lookup tc m of
            Nothing -> Right (Map.insert tc k m)
            Just k' | k == k' -> Right m
                    | otherwise -> Left (inconsErr iloc "C1" iname (showTC tc) "kind")

mergeTypesStrict :: SLoc -> String -> TypeEnv -> TypeEnv -> Either ErrMsg TypeEnv
mergeTypesStrict iloc iname old new = foldr step (Right old) (Map.toList new)
  where
    step (dc, p) acc = do
        m <- acc
        case Map.lookup dc m of
            Nothing -> Right (Map.insert dc p m)
            Just p' | p == p' -> Right m
                    | otherwise -> Left (inconsErr iloc "C2" iname (showDC dc) "type")

showTC :: TypeConstructor -> String
showTC (TC_Named s) = s
showTC tc           = show tc

showDC :: DataConstructor -> String
showDC (DC_Named s) = s
showDC dc           = show dc

mergeFixityStrict :: SLoc -> String -> NotationDB -> NotationDB -> Either ErrMsg NotationDB
mergeFixityStrict iloc iname old new = do
    _ <- mapM_
        (\(name, fp) -> case lookupFixity name old of
            Nothing -> Right ()
            Just fp' | fp == fp' -> Right ()
                     | otherwise -> Left (inconsErr iloc "C5" iname name "fixity"))
        (Notation.fixityList new)
    Right (Notation.merge old new)
  where
    lookupFixity name db = lookup name (Notation.fixityList db)

-- §2.4 C3/C4: surface-level abbreviation/notation conflicts.  We compare
-- against the ExpansionDB (TypeRep/TermRep) bodies rather than the
-- compiled TermNode templates so the error attributes the right SLoc
-- chain and so we don't have to recompile the body just to compare.
mergeExpStrict :: SLoc -> String -> ExpansionDB -> ExpansionDB -> Either ErrMsg ExpansionDB
mergeExpStrict iloc iname old new = do
    _ <- mapM_
        (\(nm, ps, rhs) -> case lookup nm [ (n', (p', r')) | (n', p', r') <- typeAbbrevs old ] of
            Nothing -> Right ()
            Just (ps', rhs') | ps == ps' && typeRepEq rhs rhs' -> Right ()
                             | otherwise -> Left (inconsErr iloc "C3" iname nm "abbreviation"))
        (typeAbbrevs new)
    _ <- mapM_
        (\(nm, ps, rhs) -> case lookup nm [ (n', (p', r')) | (n', p', r') <- termNotations old ] of
            Nothing -> Right ()
            Just (ps', rhs') | ps == ps' && termRepEq rhs rhs' -> Right ()
                             | otherwise -> Left (inconsErr iloc "C4" iname nm "notation"))
        (termNotations new)
    Right (Notation.mergeExpansion old new)
  where
    typeAbbrevs   = Notation.typeAbbrevList
    termNotations = Notation.termNotationList

inconsErr :: SLoc -> String -> String -> String -> String -> ErrMsg
inconsErr iloc tag iname dname kindLabel =
    "*** module-error[" ++ pprint 0 iloc "" ++ "]:\n"
    ++ "  ? import inconsistency (" ++ tag ++ "): `" ++ dname
    ++ "' is declared by `" ++ iname ++ "' with a different "
    ++ kindLabel ++ " than a prior import."

-- SLoc-blind structural equality on surface TypeRep / TermRep.  Two
-- imports declaring the same abbreviation/notation should be considered
-- equal even if their source positions differ.  Parenthesis nodes
-- (`RPrn`, `RTyPrn`) are transparent.
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

extractHeaderAndImports
    :: [DeclRep]
    -> Either ErrMsg (Maybe (SLoc, String), [(SLoc, String)], [DeclRep])
extractHeaderAndImports decls0 = case decls0 of
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
            (loc : _) -> Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? `import' declarations must precede all other declarations.")
            [] -> case [ loc | RModuleHeaderDecl loc _ <- rest ] of
                (loc : _) -> Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? `module' header must be the first declaration of the file.")
                [] -> return ([], rest)

liftEither :: Either ErrMsg a -> Loader a
liftEither = either throwE return
