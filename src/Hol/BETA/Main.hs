module Hol.BETA.Main where

import Hol.BETA.Answer (renderAnswer)
import Hol.BETA.Arith (installPresburgerWithEnvDiagnostic)
import Hol.BETA.Compiler
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Diagnostic
import Hol.BETA.Desugarer
import Hol.BETA.FixityResolver (FixityError (..), resolveTermWithFixity)
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.ModuleLoader (LoadedModule (..), ModuleEnv (..), loadMainWithDiagnostic, validateGoalTerm)
import Hol.BETA.Notation (NotationDB, ExpansionDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.PlanHolLexer
import Hol.BETA.PlanHolParser
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Hol.BETA.TypeChecker
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Functor.Identity (runIdentity)
import Data.Maybe
import qualified Data.List as List
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO
import qualified Z.Doc
import Z.System
import Z.Utils
import Data.IntMap (restrictKeys)

type AnalyzerOuput = Either TermRep [DeclRep]

data ReplResult
    = ReplQuit
    | ReplReload ReplControl
    deriving ()

data ReplControl
    = ReplControl
        { replDebugging :: IORef Debugging
        , replVerboseTyping :: IORef Bool
        , replNameCache :: IORef NameCache
        }
    deriving ()

data RuntimeRunner
    = RuntimeRunner
        { runtimeRun :: RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr (UniqueT ShellyT) Satisfied
        , runtimeName :: String
        }
    deriving ()

betaRuntimeRunner :: RuntimeRunner
betaRuntimeRunner = RuntimeRunner
    { runtimeRun = execRuntime
    , runtimeName = "interpreted"
    }

runAnalyzerWith :: DiagnosticMode -> NotationDB -> String -> Either ErrMsg AnalyzerOuput
runAnalyzerWith mode notationDB src0
    = case runHolLexer src0 of
        Left (row, col) -> Left (diagnosticWith mode "HolBETA-LexError" (Just (lines src0)) (SLoc (row, col) (row, col)) [Z.Doc.text "Lexing failed."])
        Right src1 -> case runHolParser src1 of
            Left Nothing -> Left (diagnosticWith mode "HolBETA-ParseError" (Just (lines src0)) (eofSLoc src0) [Z.Doc.text "Parsing failed at EOF."])
            Left (Just token) -> case getSLoc token of
                loc -> Left (diagnosticWith mode "HolBETA-ParseError" (Just (lines src0)) loc [Z.Doc.text "Parsing failed."])
            Right (Left termRep) -> case resolveTermWithFixity notationDB termRep of
                Left (FixityError loc msg) -> Left (diagnosticWith mode "HolBETA-ParseError" (Just (lines src0)) loc [Z.Doc.text "Parsing failed.", Z.Doc.text msg])
                Right output -> Right (Left output)
            Right (Right _) -> Left (diagnosticNoLocWith mode "HolBETA-ParseError" [Z.Doc.text "Expected a query, not a declaration."])

isYES :: String -> Bool
isYES str = str `elem` [ str1 ++ str2 ++ str3 | str1 <- ["Y", "y"], str2 <- ["", "es"], str3 <- if null str2 then [""] else ["", "."] ]

addIndex :: [Fact] -> Either KernelErr (Map.Map Constant [Fact])
addIndex facts = foldM addFact Map.empty [ rewrite NF f0 | f <- facts, f0 <- expandAssumptions f ] where
    addFact index fact = case hd fact of
        Just predicate -> Right (Map.insertWith (\new old -> old ++ new) predicate [fact] index)
        Nothing -> Left (BadFactGiven fact)
    hd :: Fact -> Maybe Constant
    hd t = case unfoldlNApp t of
        (NLam _ _ t _, _) -> hd t
        (NCon (DC (DC_LO LO_ty_pi)) _, [t]) -> hd t
        (NCon (DC (DC_LO LO_pi)) _, [t]) -> hd t
        (NCon (DC (DC_LO LO_if)) _, [t, _]) -> hd t
        (NCon c _, _) -> Just c
        _ -> Nothing

execRuntime :: UniqueM m => RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntime env isDebugging facts query = do
    call_id <- getUnique
    factIndex <- either throwE return (addIndex facts)
    let namedTypes = Map.fromList [ (nm, ty) | (LV_Named nm, ty) <- Map.toList (_TypeInfo env) ]
        initialLabeling = Labeling { _ConLabel = IntMap.empty, _VarLabel = IntMap.empty, _ConTypes = IntMap.empty, _VarTypes = IntMap.empty, _NamedTypes = namedTypes, _TyVarKeys = IntMap.empty, _TypeEnv = _ProgramTypeEnv env}
        initialContext = Context { _TotalVarBinding = mempty, _CurrentLabeling = initialLabeling, _LeftConstraints = [], _ContextThreadId = call_id, _debuggindModeOn = isDebugging }
    runTransition (env { _QueryCallId = Just call_id }) (getLVars query) [(initialContext, [Cell { _GivenFacts = factIndex, _GivenHypos = [], _GivenArithPremises = ([], []), _ScopeLevel = 0, _WantedGoal = query, _CellCallId = call_id }])]

runREPL :: DiagnosticMode -> Program TermNode -> NotationDB -> ExpansionDB -> UniqueT ShellyT ReplResult
runREPL = runREPLWith betaRuntimeRunner

runREPLWith :: RuntimeRunner -> DiagnosticMode -> Program TermNode -> NotationDB -> ExpansionDB -> UniqueT ShellyT ReplResult
runREPLWith runner mode program notationDB expansionDB = do
    control <- liftIO $ ReplControl <$> newIORef False <*> newIORef False <*> newIORef initialCache
    runREPLWithControlAndRunner runner mode program notationDB expansionDB control

runREPLWithControl :: DiagnosticMode -> Program TermNode -> NotationDB -> ExpansionDB -> ReplControl -> UniqueT ShellyT ReplResult
runREPLWithControl = runREPLWithControlAndRunner betaRuntimeRunner

runREPLWithControlAndRunner :: RuntimeRunner -> DiagnosticMode -> Program TermNode -> NotationDB -> ExpansionDB -> ReplControl -> UniqueT ShellyT ReplResult
runREPLWithControlAndRunner runner mode program notationDB expansionDB control
    = go (replDebugging control) (replVerboseTyping control) (replNameCache control)
    where
        go :: IORef Debugging -> IORef Bool -> IORef NameCache -> UniqueT ShellyT ReplResult
        go isDebugging verboseTyping nameCache = do
            query <- lift $ promptifyM ""
            case query of
                "" -> do
                    lift $ shellyM "Hol >>= quit"
                    return ReplQuit
                ":q" -> do
                    lift $ shellyM "Hol >>= quit"
                    return ReplQuit
                ":reload" -> do
                    lift $ shellyM "Hol >>= reload"
                    return (ReplReload control)
                ":d" -> do
                    lift $ do
                        liftIO $ modifyIORef isDebugging not
                        debugging <- liftIO $ readIORef isDebugging
                        shellyM (moduleName program ++ "> " ++ "Debugging mode " ++ (if debugging then "on" else "off") ++ ".")
                    go isDebugging verboseTyping nameCache
                ":short" -> do
                    lift $ do
                        liftIO $ writeIORef verboseTyping False
                        shellyM (moduleName program ++ "> " ++ "Typing display: short.")
                    go isDebugging verboseTyping nameCache
                ":verbose" -> do
                    lift $ do
                        liftIO $ writeIORef verboseTyping True
                        shellyM (moduleName program ++ "> " ++ "Typing display: verbose.")
                    go isDebugging verboseTyping nameCache
                query0 -> case runAnalyzerWith mode notationDB query0 of
                    Left err_msg -> do
                        liftIO $ putStrLn err_msg
                        go isDebugging verboseTyping nameCache
                    Right output -> case output of
                        Left query1 -> do
                            result <- runExceptT $ do
                                (query2, free_vars) <- desugarQuery (Notation.expandTermRep expansionDB query1)
                                (query3, (used_mtvs, assumptions)) <- checkTypeWithDiagnostic mode (Just (lines query0)) notationDB (_TypeDecls program) query2 mkTyO
                                let freeVarEnv = Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]
                                    presburgerEnv = Map.fromList [ (name, term) | (name, ivar) <- Map.toList free_vars, Just term <- [Map.lookup ivar freeVarEnv] ]
                                query4 <- convertQuery used_mtvs assumptions freeVarEnv query3
                                query5 <- either throwE return (installPresburgerWithEnvDiagnostic mode (Just (moduleName program)) (Just (lines query0)) presburgerEnv query4)
                                either (throwE . invalidGoalDiagnostic "HolBETA-GoalError" query0 query5) return (validateGoalTerm query5)
                                let typeMap = Map.fromList
                                        [ (LV_Named name, typ)
                                        | (name, ivar) <- Map.toList free_vars
                                        , Just typ <- [Map.lookup ivar assumptions]
                                        ]
                                return (query5, typeMap)
                            case result of
                                Left err_msg -> do
                                    liftIO $ putStrLn err_msg
                                    go isDebugging verboseTyping nameCache
                                Right (query4, typeMap) -> do
                                    pendingSubst <- liftIO $ newIORef (VarBinding Map.empty)
                                    runtime_env <- liftIO $ mkRuntimeEnv isDebugging verboseTyping nameCache pendingSubst typeMap query4
                                    answer <- runExceptT (runtimeRun runner runtime_env isDebugging (_FactDecls program) query4)
                                    case answer of
                                        Left runtime_err -> case runtime_err of
                                            BadGoalGiven t -> liftIO $ putStrLn (runtimeDiagnostic (Just (lines query0)) t [Z.Doc.text "Bad goal given."])
                                            BadFactGiven t -> liftIO $ putStrLn (runtimeDiagnostic Nothing t [Z.Doc.text "Bad fact given."])
                                            UnsupportedArithmeticConstraint t -> liftIO $ putStrLn (runtimeDiagnostic (Just (lines query0)) t [Z.Doc.text "Unsupported arithmetic constraint.", Z.Doc.text "Only ground constraints and linear Presburger constraints can be used with comparison predicates.", Z.Doc.text ("Constraint: " ++ shows t "")])
                                            BackendError message -> liftIO $ putStrLn (diagnosticNoLocWith mode "HolV1-BytecodeError" [Z.Doc.text message])
                                        Right sat -> do
                                            liftIO $ promptify (if sat then "yes." else "no.")
                                            return ()
                                    go isDebugging verboseTyping nameCache
                        Right src1 -> do
                            liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA-ParseError" [Z.Doc.text "It is not a query."])
                            go isDebugging verboseTyping nameCache

        runtimeDiagnostic :: SourceLines -> TermNode -> [Z.Doc.Doc] -> String
        runtimeDiagnostic sourceLines term body = case getNodeSLoc term of
            Just loc -> diagnosticWithModule mode "HolBETA-RuntimeError" (Just (moduleName program)) sourceLines loc body
            Nothing -> diagnosticNoLocWith mode "HolBETA-RuntimeError" body

        invalidGoalDiagnostic :: String -> String -> TermNode -> TermNode -> ErrMsg
        invalidGoalDiagnostic tag source fallback bad =
            let body =
                    [ Z.Doc.text "Malformed goal or local implication."
                    , Z.Doc.text "A local antecedent must be a named-predicate clause or a supported arithmetic assumption (or a conjunction of them), and a clause body must contain executable goals."
                    ]
                sourceLines = Just (lines source)
            in case getNodeSLoc bad `mplus` getNodeSLoc fallback of
                Just loc -> diagnosticWithModule mode tag (Just (moduleName program)) sourceLines loc body
                Nothing -> diagnosticNoLocWith mode tag body

        promptify :: String -> IO String
        promptify str = shelly (moduleName program ++ "> " ++ str)
        promptifyM :: String -> ShellyT String
        promptifyM str = shellyM (moduleName program ++ "> " ++ str)
        mkRuntimeEnv :: IORef Debugging -> IORef Bool -> IORef NameCache -> IORef LogicVarSubst -> Map.Map LogicVar (MonoType Int) -> TermNode -> IO RuntimeEnv
        mkRuntimeEnv isDebugging verboseTyping nameCache pendingSubst typeMap query
            = do
                stackRef <- newIORef []
                return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer, _PrintPrimitive = primitivePrint, _ReadPrimitive = primitiveRead, _TypeInfo = typeMap, _PendingSubst = pendingSubst, _ProgramKindEnv = _KindDecls program, _ProgramTypeEnv = _TypeDecls program, _VerboseTyping = verboseTyping, _StackRef = stackRef, _NameCacheRef = nameCache, _DebuggingRef = isDebugging, _NotationDB = notationDB, _ModuleName = moduleName program, _QueryCallId = Nothing })
            where
                primitivePrint :: Context -> TermNode -> IO ()
                primitivePrint ctx term = do
                    cache <- readIORef nameCache
                    let pp = prettyTerm notationDB cache
                    _ <- promptify (pp (bindVars (_TotalVarBinding ctx) term) "")
                    return ()
                primitiveRead :: Context -> TermNode -> IO (Maybe TermNode)
                primitiveRead ctx term = do
                    src <- promptify "read> "
                    return (parsePrimitiveInput (expectedType ctx term) src)
                expectedType :: Context -> TermNode -> Maybe (MonoType Int)
                expectedType ctx term
                    = case bindVars (_TotalVarBinding ctx) (rewrite NF term) of
                        LVar lv -> lookupLVarType lv (_CurrentLabeling ctx) `mplus` Map.lookup lv typeMap
                        _ -> Nothing
                parsePrimitiveInput :: Maybe (MonoType Int) -> String -> Maybe TermNode
                parsePrimitiveInput (Just ty)
                    | ty == mkTyNat = parseNat
                    | ty == mkTyChr = parseChr
                    | ty == mkTyList mkTyChr = parseStr
                parsePrimitiveInput _ = \src -> parseNat src `mplus` parseChr src `mplus` parseStr src
                parseNat :: String -> Maybe TermNode
                parseNat src
                    | not (null src) && all isDecimalDigit src = case reads src of
                        [(n, "")] -> Just (mkNCon (DC_NatL (n :: Integer)))
                        _ -> Nothing
                    | otherwise = Nothing
                    where
                        isDecimalDigit ch = '0' <= ch && ch <= '9'
                parseChr :: String -> Maybe TermNode
                parseChr src = mkNCon . DC_ChrL <$> readHolCharLiteral src
                parseStr :: String -> Maybe TermNode
                parseStr src = stringTerm <$> readHolStringLiteral src
                stringTerm :: String -> TermNode
                stringTerm = foldr cons (mkNApp (mkNCon DC_Nil) charType) where
                    charType = mkNCon (TC_Named "char")
                    cons ch acc = mkNApp (mkNApp (mkNApp (mkNCon DC_Cons) charType) (mkNCon (DC_ChrL ch))) acc
                runInteraction :: RuntimeEnv -> Context -> String -> IO ()
                runInteraction env ctx str = do
                    isDebugging <- readIORef (_debuggindModeOn ctx)
                    when isDebugging $ do
                        putStrLn str
                        response <- promptify "Press the enter key to go to next state: "
                        case response of
                            ":d" -> do
                                runRuntime cmdDebugToggle env
                                debugging <- readIORef (_DebuggingRef env)
                                _ <- promptify (if debugging then "Debugging mode on." else "Debugging mode off.")
                                return ()
                            ":short" -> do
                                writeIORef verboseTyping False
                                promptify "Typing display: short."
                                return ()
                            ":verbose" -> do
                                writeIORef verboseTyping True
                                promptify "Typing display: verbose."
                                return ()
                            ":reload" -> do
                                _ <- promptify (diagnosticNoLocWith mode "HolBETA-REPLError" [Z.Doc.text "`:reload' is not available inside `:debug' mode or while a query is searching for answers."])
                                return ()
                            _
                                | (":assign " `List.isPrefixOf` response) ->
                                    handleAssign env ctx (drop (length (":assign " :: String)) response)
                            _
                                | (":show " `List.isPrefixOf` response) -> do
                                    let body = drop (length (":show " :: String)) response
                                        trimmed = dropWhile (== ' ') body
                                        varName = case trimmed of
                                            '?' : rest -> rest
                                            _ -> trimmed
                                    result <- runRuntime (cmdShow varName) env
                                    _ <- promptify ("*** :show: ?" ++ varName ++ " = " ++ result)
                                    return ()
                            _ -> return ()
                parseAssign :: String -> Maybe (String, String)
                parseAssign body0
                    = case body of
                        '?' : rest -> findSep rest ""
                        _ -> Nothing
                    where
                        body = dropWhile (== ' ') body0

                        findSep :: String -> String -> Maybe (String, String)
                        findSep [] _ = Nothing
                        findSep (' ' : ':' : '=' : ' ' : rs) acc =
                            Just (reverse (dropWhile (== ' ') acc), dropWhile (== ' ') rs)
                        findSep (c : cs) acc = findSep cs (c : acc)
                handleAssign :: RuntimeEnv -> Context -> String -> IO ()
                handleAssign env ctx body = case parseAssign body of
                    Nothing -> do
                        _ <- promptify (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text "Expected ':assign ?X := t.'."])
                        return ()
                    Just (varName, tBody) -> do
                        let queryStr = "?- " ++ varName ++ " = " ++ rewriteAssignSource tBody
                        cache <- readIORef nameCache
                        result <- execUniqueT $ runExceptT (compileAssign varName queryStr)
                        case result of
                            Left err -> do
                                _ <- promptify err
                                return ()
                            Right (compiledLV, t_compiled, inferredTy, nameToType) -> do
                                let labelingForCheck = _CurrentLabeling ctx
                                    isKnownTarget lv = case lv of
                                        LV_Named _ -> isJust (lookupLVarType lv labelingForCheck) || Map.member lv typeMap
                                        LV_Unique uni _ -> IntMap.member (unUnique uni) (_VarLabel labelingForCheck)
                                        LV_ty_var uni -> IntMap.member (unUnique uni) (_VarLabel labelingForCheck)
                                    resolveDisplayName nm = do
                                        lv <- fromDisplay nm cache `mplus` parseAnonymousLV nm `mplus` Just (LV_Named nm)
                                        guard (isKnownTarget lv)
                                        return lv
                                    resolvedTarget = resolveDisplayName varName
                                    targetLV = fromMaybe compiledLV resolvedTarget
                                    xconNames =
                                        [ (nm, uni)
                                        | LV_Named nm <- Set.toList (getLVars t_compiled)
                                        , Just uni <- [parseXcon nm]
                                        ]
                                    xconErrors = concat
                                        [ case IntMap.lookup uni (_ConTypes labelingForCheck) of
                                            Nothing -> ["'c_" ++ show uni ++ "' is not a known rigid constant in this state"]
                                            Just _ -> []
                                        | (nm, uni) <- xconNames
                                        ]
                                    lvarErrors =
                                        [ "'?" ++ nm ++ "' is not an active debugger variable"
                                        | LV_Named nm <- Set.toList (getLVars t_compiled)
                                        , Nothing <- [parseXcon nm]
                                        , Nothing <- [resolveDisplayName nm]
                                        ]
                                    xconSwap = Map.fromList
                                        [ (LV_Named nm, mkNCon (DC_Unique (Unique uni) noHint))
                                        | (nm, uni) <- xconNames
                                        ]
                                    lvarSwap = Map.fromList
                                        [ (lv, mkLVar resolved)
                                        | lv@(LV_Named nm) <- Set.toList (getLVars t_compiled)
                                        , Nothing <- [parseXcon nm]
                                        , Just resolved <- [resolveDisplayName nm]
                                        , resolved /= lv
                                        ]
                                    nameSwap = VarBinding (xconSwap `Map.union` lvarSwap)
                                    t_resolved = bindVars nameSwap t_compiled
                                    mexpectedTy = lookupLVarType targetLV labelingForCheck `mplus` Map.lookup targetLV typeMap
                                    runtimeTypeChecks =
                                        [ ("?" ++ varName, inferredTy, actual)
                                        | actual <- maybeToList mexpectedTy
                                        ]
                                        ++ [ ("c_" ++ show uni, inferred, actual)
                                            | (nm, uni) <- xconNames
                                            , actual <- maybeToList (IntMap.lookup uni (_ConTypes labelingForCheck))
                                            , inferred <- maybeToList (Map.lookup nm nameToType)
                                            ]
                                        ++ [ ("?" ++ nm, inferred, actual)
                                            | LV_Named nm <- Set.toList (getLVars t_compiled)
                                            , Nothing <- [parseXcon nm]
                                            , Just resolved <- [resolveDisplayName nm]
                                            , actual <- maybeToList (lookupLVarType resolved labelingForCheck `mplus` Map.lookup resolved typeMap)
                                            , inferred <- maybeToList (Map.lookup nm nameToType)
                                            ]
                                    runtimeTypesAgree = typesJointlyCompatible
                                        [ (inferred, separateRuntimeMTVs actual)
                                        | (_, inferred, actual) <- runtimeTypeChecks
                                        ]
                                    runtimeTypeSummary = List.intercalate "; "
                                        [ label ++ " : " ++ showsMonoType notationDB 0 actual ""
                                        | (label, _, actual) <- runtimeTypeChecks
                                        ]
                                if isNothing resolvedTarget then do
                                    _ <- promptify (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text ("Unknown or inactive debugger variable '?" ++ varName ++ "'.")])
                                    return ()
                                else if not (null (xconErrors ++ lvarErrors)) then do
                                    _ <- promptify (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text (List.intercalate "; " (xconErrors ++ lvarErrors))])
                                    return ()
                                else if not runtimeTypesAgree then do
                                    _ <- promptify (diagnosticNoLocWith mode "HolBETA-AssignError"
                                        [ Z.Doc.text "The assignment is inconsistent with the active debugger variable types."
                                        , Z.Doc.text runtimeTypeSummary
                                        ])
                                    return ()
                                else do
                                    result <- runRuntime (cmdAssignVar targetLV t_resolved) env
                                    case result of
                                        Left err -> do
                                            _ <- promptify (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text err])
                                            return ()
                                        Right () -> do
                                            composed_subst <- do
                                                ep <- readIORef pendingSubst
                                                return (ep <> _TotalVarBinding ctx)
                                            let t_zonked = bindVars composed_subst t_resolved
                                                pp = prettyTerm notationDB cache
                                            _ <- promptify ("*** :assign: " ++ pp (mkLVar targetLV) (" := " ++ pp t_zonked "."))
                                            return ()
                rewriteAssignSource :: String -> String
                rewriteAssignSource = go Nothing False where
                    isIdChar c = c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "_")
                    isDigitC c = c `elem` ['0' .. '9']
                    go _ _ [] = []
                    go (Just quote) escaped (c : rest)
                        | escaped = c : go (Just quote) False rest
                        | c == '\\' = c : go (Just quote) True rest
                        | c == quote = c : go Nothing False rest
                        | otherwise = c : go (Just quote) False rest
                    go Nothing _ ('?' : rest) = go Nothing False rest
                    go Nothing _ (c : rest)
                        | c == '\'' || c == '"' = c : go (Just c) False rest
                        | not (isIdChar c) = c : go Nothing False rest
                        | otherwise = case span isIdChar str of
                            (ident, rest') -> rewrite ident ++ go Nothing False rest'
                        where
                            str = c : rest
                    rewrite ident = case ident of
                        'c' : '_' : ds
                            | not (null ds) && all isDigitC ds -> "XCON_" ++ ds
                        _ -> ident
                parseXcon :: LargeId -> Maybe Int
                parseXcon nm = case nm of
                    'X' : 'C' : 'O' : 'N' : '_' : rest -> case reads rest of
                        [(n, "")] -> Just n
                        _ -> Nothing
                    _ -> Nothing
                typesJointlyCompatible :: [(MonoType Int, MonoType Int)] -> Bool
                typesJointlyCompatible pairs = case runIdentity (runExceptT (unify pairs)) of
                    Left _ -> False
                    Right _ -> True
                separateRuntimeMTVs :: MonoType Int -> MonoType Int
                separateRuntimeMTVs typ = case typ of
                    TyVar idx -> TyVar idx
                    TyCon con -> TyCon con
                    TyApp fun arg -> TyApp (separateRuntimeMTVs fun) (separateRuntimeMTVs arg)
                    TyMTV uni -> TyMTV (Unique (negate (unUnique uni) - 1))
                compileAssign :: MonadUnique m => String -> String -> ExceptT ErrMsg m (LogicVar, TermNode, MonoType Int, Map.Map LargeId (MonoType Int))
                compileAssign varName queryStr = case runHolLexer queryStr of
                    Left (row, col) -> throwE (diagnosticWith mode "HolBETA-AssignError" (Just (lines queryStr)) (SLoc (row, col) (row, col)) [Z.Doc.text "Lexing failed."])
                    Right tokens -> case runHolParser tokens of
                        Left Nothing -> throwE (diagnosticWith mode "HolBETA-AssignError" (Just (lines queryStr)) (eofSLoc queryStr) [Z.Doc.text "Parsing failed at EOF."])
                        Left (Just token) -> throwE (diagnosticWith mode "HolBETA-AssignError" (Just (lines queryStr)) (getSLoc token) [Z.Doc.text "Parsing failed."])
                        Right (Right _) -> throwE (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text "Expected a query, not a declaration."])
                        Right (Left termRep0) -> do
                            termRep <- case resolveTermWithFixity notationDB termRep0 of
                                Left (FixityError loc msg) -> throwE (diagnosticWith mode "HolBETA-AssignError" (Just (lines queryStr)) loc [Z.Doc.text "Parsing failed.", Z.Doc.text msg])
                                Right termRep -> return termRep
                            (term2, free_vars) <- desugarQuery (Notation.expandTermRep expansionDB termRep)
                            (term3, (used_mtvs, assumptions)) <- checkTypeWithDiagnostic mode (Just (lines queryStr)) notationDB (_TypeDecls program) term2 mkTyO
                            let freeVarEnv = Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]
                                presburgerEnv = Map.fromList [ (name, term) | (name, ivar) <- Map.toList free_vars, Just term <- [Map.lookup ivar freeVarEnv] ]
                            term4 <- convertQuery used_mtvs assumptions freeVarEnv term3
                            term5 <- either throwE return (installPresburgerWithEnvDiagnostic mode (Just (moduleName program)) (Just (lines queryStr)) presburgerEnv term4)
                            inferredTy <- case Map.lookup varName free_vars >>= \ivar -> Map.lookup ivar assumptions of
                                Just typ -> return typ
                                Nothing -> throwE (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text "Could not infer type for the binding."])
                            let nameToType = Map.fromList [ (nm, ty) | (nm, ivar) <- Map.toList free_vars , Just ty <- [Map.lookup ivar assumptions] ]
                            case unfoldlNApp (rewrite NF term5) of
                                (NCon (DC DC_eq) _, [_typeArg, lhs, rhs]) -> case rewrite NF lhs of
                                    LVar lv -> do
                                        when (inferredTy == mkTyO) $
                                            either (throwE . invalidGoalDiagnostic "HolBETA-AssignError" queryStr rhs) return (validateGoalTerm rhs)
                                        return (lv, rhs, inferredTy, nameToType)
                                    _ -> throwE (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text "LHS did not resolve to a logic variable."])
                                _ -> throwE (diagnosticNoLocWith mode "HolBETA-AssignError" [Z.Doc.text "Did not compile to an equality."])
                printAnswer :: Context -> IO RunMore
                printAnswer ctx = do
                    cache <- readIORef nameCache
                    printAnswerWithCache cache ctx
                printAnswerWithCache :: NameCache -> Context -> IO RunMore
                printAnswerWithCache cache ctx = case renderAnswer notationDB cache query ctx of
                    Nothing -> return True
                    Just [] -> return False
                    Just answerLines -> mapM_ promptify answerLines >> askToRunMore
                    where
                        askToRunMore :: IO RunMore
                        askToRunMore = do
                            str <- promptify "Find more solutions? [Y/n] "
                            if List.null str then
                                askToRunMore
                            else if str == ":reload" then do
                                _ <- promptify (diagnosticNoLocWith mode "HolBETA-REPLError" [Z.Doc.text "`:reload' is not available inside `:debug' mode or while a query is searching for answers."])
                                askToRunMore
                            else
                                return (isYES str)

theInitialKindDecls :: KindEnv
theInitialKindDecls = Map.fromList
    [ (TC_Arrow, read "* -> * -> *")
    , (TC_Named "list", read "* -> *")
    , (TC_Named "o", read "*")
    , (TC_Named "char", read "*")
    , (TC_Named "nat", read "*")
    , (TC_Named "string", read "*")
    ]

theInitialTypeDecls :: TypeEnv
theInitialTypeDecls = Map.fromList
    [ (DC_LO LO_if, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_and, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_or, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_imply, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_sigma, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_pi, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_cut, Forall [] (mkTyO))
    , (DC_LO LO_true, Forall [] (mkTyO))
    , (DC_LO LO_fail, Forall [] (mkTyO))
    , (DC_LO LO_is, Forall ["A"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    , (DC_LO LO_debug, Forall [] (mkTyList mkTyChr `mkTyArrow` mkTyO))
    , (DC_Nil, Forall ["A"] (mkTyList (TyVar 0)))
    , (DC_Cons, Forall ["A"] (TyVar 0 `mkTyArrow` (mkTyList (TyVar 0) `mkTyArrow` mkTyList (TyVar 0))))
    , (DC_Succ, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_eq, Forall ["A"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    , (DC_ge, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_gt, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_le, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_lt, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_plus, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_minus, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_mul, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_div, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Named "presburger", Forall [] (mkTyList mkTyChr `mkTyArrow` mkTyO))
    , (DC_Named "print", Forall ["A"] (TyVar 0 `mkTyArrow` mkTyO))
    , (DC_Named "read", Forall ["A"] (TyVar 0 `mkTyArrow` mkTyO))
    , (DC_Named "flex", Forall ["A"] (TyVar 0 `mkTyArrow` mkTyO))
    ]

theInitialFactDecls :: [TermNode]
theInitialFactDecls = [eqFact] where
    mtv_eq :: MetaTVar
    mtv_eq = Unique (-1)
    eqFact :: TermNode
    eqFact = mkNApp (mkNCon LO_ty_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv_eq)) (mkNApp (mkNCon LO_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv_eq)) (mkNApp (mkNApp (mkNApp (mkNCon DC_eq) (mkNIdx 1)) (mkNIdx 0)) (mkNIdx 0)))))

theDefaultModuleName :: String
theDefaultModuleName = "Hol"

runHol :: DiagnosticMode -> UniqueT ShellyT ()
runHol = runHolWith betaRuntimeRunner

runHolWith :: RuntimeRunner -> DiagnosticMode -> UniqueT ShellyT ()
runHolWith runner mode = do
    consistency_ptr <- liftIO $ newIORef ""
    file_dir <- lift $ shellyM "Hol =<< "
    maybe_file_name <- case file_dir of
        ":q" -> do
            liftIO $ writeIORef consistency_ptr ":q"
            return Nothing
        _ -> case matchFileDirWithExtension file_dir of
            ("", "") -> return Nothing
            (file_name, ".hol") -> return (Just file_name)
            (file_name, "") -> return (Just file_name)
            (file_name, '.' : wrong_extension) -> do
                liftIO $ writeIORef consistency_ptr (theDefaultModuleName ++ "> " ++ shows wrong_extension " is a non-executable file extension.")
                return Nothing
    consistency <- liftIO $ readIORef consistency_ptr
    case consistency of
        "" -> case maybe_file_name of
            Nothing -> do
                lift $ shellyM (theDefaultModuleName ++ "> Ok, no module loaded.")
                replResult <- runREPLWith runner mode (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName }) Notation.initial Notation.initialExpansionDB
                case replResult of
                    ReplQuit -> return ()
                    ReplReload _ -> runHolWith runner mode
            Just file_name -> runHolFileWith runner mode file_name
        inconsistent_proof -> do
            if inconsistent_proof == ":q"
                then do
                    _ <- lift $ shellyM ("Hol >>= quit")
                    return ()
                else do
                    lift $ shellyM inconsistent_proof
                    lift $ shellyM ("Hol >>= quit")
                    return ()

runHolFile :: DiagnosticMode -> String -> UniqueT ShellyT ()
runHolFile = runHolFileWith betaRuntimeRunner

runHolFileWith :: RuntimeRunner -> DiagnosticMode -> String -> UniqueT ShellyT ()
runHolFileWith runner mode file_name = attemptLoad Nothing where
    my_file_dir = file_name ++ ".hol"
    myModuleName = modifySep '/' (const ".") id file_name

    attemptLoad fallback = do
        msrc <- liftIO $ readFileNow my_file_dir
        case msrc of
            Nothing -> loadFailed fallback
                (diagnosticNoLocWith mode "HolBETA-FileError" [Z.Doc.text ("Cannot read file `" ++ my_file_dir ++ "'.")])
            Just _ -> do
                file_abs_dir <- fmap (fromMaybe my_file_dir) (liftIO $ makePathAbsolutely my_file_dir)
                lift $ shellyM (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", " ++ runtimeName runner ++ " )")
                result <- loadMainWithDiagnostic mode theInitialKindDecls theInitialTypeDecls theInitialFactDecls my_file_dir
                case result of
                    Left err_msg -> loadFailed fallback err_msg
                    Right loaded -> do
                        liftIO $ mapM_ putStrLn (loadedWarnings loaded)
                        let mainEnv = loadedMain loaded
                            program = Program
                                { _KindDecls  = moduleEnvKinds mainEnv
                                , _TypeDecls  = moduleEnvTypes mainEnv
                                , _FactDecls  = moduleEnvFacts mainEnv
                                , moduleName  = moduleEnvName mainEnv
                                }
                            active = (program, moduleEnvNotation mainEnv, moduleEnvExpansion mainEnv)
                        lift $ shellyM (moduleEnvName mainEnv ++ "> Ok, one module loaded.")
                        replResult <- runREPLWith runner mode program (moduleEnvNotation mainEnv) (moduleEnvExpansion mainEnv)
                        handleRepl active replResult

    loadFailed Nothing err_msg = do
        liftIO $ putStrLn err_msg
        runHolWith runner mode
    loadFailed (Just (active, control)) err_msg = do
        -- A failed reload is atomic: keep both the old export environment and
        -- its top-level presentation/debug controls.  A successful reload
        -- above starts a fresh `runREPL' and therefore a fresh generation.
        liftIO $ putStrLn err_msg
        resume active control

    handleRepl _ ReplQuit = return ()
    handleRepl active (ReplReload control) = attemptLoad (Just (active, control))

    resume active@(program, notationDB, expansionDB) control = do
        replResult <- runREPLWithControlAndRunner runner mode program notationDB expansionDB control
        handleRepl active replResult

mainWithModeM :: DiagnosticMode -> ShellyT ()
mainWithModeM = mainWithRunnerM betaRuntimeRunner

mainWithRunnerM :: RuntimeRunner -> DiagnosticMode -> ShellyT ()
mainWithRunnerM runner = execUniqueT . runHolWith runner

mainWithMode :: DiagnosticMode -> IO ()
mainWithMode = runShellyT . mainWithModeM

mainWithArgsM :: [String] -> ShellyT ()
mainWithArgsM args
    = case args of
        [] -> mainWithModeM DiagnosticPretty
        ["pretty"] -> mainWithModeM DiagnosticPretty
        ["test"] -> mainWithModeM DiagnosticTest
        _ -> mainWithModeM DiagnosticPretty

mainWithArgs :: [String] -> IO ()
mainWithArgs = runShellyT . mainWithArgsM

main :: IO ()
main = mainWithMode DiagnosticPretty
