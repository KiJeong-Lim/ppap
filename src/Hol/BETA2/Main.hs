module Hol.BETA2.Main where

import Hol.BETA2.Arith (arithEntails, installPresburger)
import Hol.BETA2.Compiler
import Hol.BETA2.Constant
import Hol.BETA2.Debugger
import Hol.BETA2.Diagnostic
import Hol.BETA2.Desugarer
import Hol.BETA2.FixityResolver (FixityError (..), resolveTermWithFixity)
import Hol.BETA2.Header
import Hol.BETA2.HOPU
import Hol.BETA2.ModuleLoader (LoadedModule (..), ModuleEnv (..), loadMainWithDiagnostic)
import Hol.BETA2.Notation (NotationDB, ExpansionDB)
import qualified Hol.BETA2.Notation as Notation
import Hol.BETA2.PlanHolLexer
import Hol.BETA2.PlanHolParser
import Hol.BETA2.Runtime
import Hol.BETA2.TermNode
import Hol.BETA2.TypeChecker
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
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
    | ReplReload

runAnalyzerWith :: DiagnosticMode -> NotationDB -> String -> Either ErrMsg AnalyzerOuput
runAnalyzerWith mode notationDB src0
    = case runHolLexer src0 of
        Left (row, col) -> Left (diagnosticWith mode "HolBETA2-LexError" (Just (lines src0)) (SLoc (row, col) (row, col)) [Z.Doc.text "Lexing failed."])
        Right src1 -> case runHolParser src1 of
            Left Nothing -> Left (diagnosticNoLocWith mode "HolBETA2-ParseError" [Z.Doc.text "Parsing failed at EOF."])
            Left (Just token) -> case getSLoc token of
                loc -> Left (diagnosticWith mode "HolBETA2-ParseError" (Just (lines src0)) loc [Z.Doc.text "Parsing failed."])
            Right (Left termRep) -> case resolveTermWithFixity notationDB termRep of
                Left (FixityError loc msg) -> Left (diagnosticWith mode "HolBETA2-ParseError" (Just (lines src0)) loc [Z.Doc.text "Parsing failed.", Z.Doc.text msg])
                Right output -> Right (Left output)
            Right (Right _) -> Left (diagnosticNoLocWith mode "HolBETA2-ParseError" [Z.Doc.text "Parsing failed at EOF."])

isYES :: String -> Bool
isYES str = str `elem` [ str1 ++ str2 ++ str3 | str1 <- ["Y", "y"], str2 <- ["", "es"], str3 <- if null str2 then [""] else ["", "."] ]

addIndex :: [Fact] -> Map.Map Constant [Fact]
addIndex facts = Map.fromListWith (\new old -> old ++ new) [ (hd f', [f']) | f <- facts, f0 <- expandAssumptions f, let f' = rewrite NF f0 ] where
    hd :: Fact -> Constant
    hd t = case unfoldlNApp t of
        (NLam _ _ t _, _) -> hd t
        (NCon (DC (DC_LO LO_ty_pi)) _, [t]) -> hd t
        (NCon (DC (DC_LO LO_pi)) _, [t]) -> hd t
        (NCon (DC (DC_LO LO_if)) _, [t, _]) -> hd t
        (NCon c _, _) -> c

execRuntime :: UniqueM m => RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntime env isDebugging facts query = do
    call_id <- getUnique
    let namedTypes = Map.fromList [ (nm, ty) | (LV_Named nm, ty) <- Map.toList (_TypeInfo env) ]
        initialLabeling = Labeling { _ConLabel = IntMap.empty, _VarLabel = IntMap.empty, _ConTypes = IntMap.empty, _VarTypes = IntMap.empty, _NamedTypes = namedTypes, _TyVarKeys = IntMap.empty, _TypeEnv = _ProgramTypeEnv env}
        initialContext = Context { _TotalVarBinding = mempty, _CurrentLabeling = initialLabeling, _LeftConstraints = [], _ContextThreadId = call_id, _debuggindModeOn = isDebugging }
    runTransition env (getLVars query) [(initialContext, [Cell { _GivenFacts = addIndex facts, _GivenHypos = [], _ScopeLevel = 0, _WantedGoal = query, _CellCallId = call_id }])]

runREPL :: DiagnosticMode -> Program TermNode -> NotationDB -> ExpansionDB -> UniqueT ShellyT ReplResult
runREPL mode program notationDB expansionDB
    = do
        isDebugging <- liftIO (newIORef False)
        verboseTyping <- liftIO (newIORef False)
        nameCache <- liftIO (newIORef initialCache)
        go isDebugging verboseTyping nameCache
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
                    return ReplReload
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
                                query4 <- convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) query3
                                query5 <- either throwE return (installPresburger query4)
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
                                    answer <- runExceptT (execRuntime runtime_env isDebugging (_FactDecls program) query4)
                                    case answer of
                                        Left runtime_err -> case runtime_err of
                                            BadGoalGiven _ -> liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA2-RuntimeError" [Z.Doc.text "Bad goal given."])
                                            BadFactGiven _ -> liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA2-RuntimeError" [Z.Doc.text "Bad fact given."])
                                            UnsupportedArithmeticConstraint t -> liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA2-RuntimeError" [Z.Doc.text "Unsupported arithmetic constraint.", Z.Doc.text "Only ground constraints and linear Presburger constraints can be used with comparison predicates.", Z.Doc.text ("Constraint: " ++ shows t "")])
                                        Right sat -> do
                                            liftIO $ promptify (if sat then "yes." else "no.")
                                            return ()
                                    go isDebugging verboseTyping nameCache
                        Right src1 -> do
                            liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA2-ParseError" [Z.Doc.text "It is not a query."])
                            go isDebugging verboseTyping nameCache

        myTabs :: String
        myTabs = ""
        promptify :: String -> IO String
        promptify str = shelly (moduleName program ++ "> " ++ str)
        promptifyM :: String -> ShellyT String
        promptifyM str = shellyM (moduleName program ++ "> " ++ str)
        mkRuntimeEnv :: IORef Debugging -> IORef Bool -> IORef NameCache -> IORef LogicVarSubst -> Map.Map LogicVar (MonoType Int) -> TermNode -> IO RuntimeEnv
        mkRuntimeEnv isDebugging verboseTyping nameCache pendingSubst typeMap query
            = do
                stackRef <- newIORef []
                return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer, _PrintPrimitive = primitivePrint, _ReadPrimitive = primitiveRead, _TypeInfo = typeMap, _PendingSubst = pendingSubst, _ProgramTypeEnv = _TypeDecls program, _VerboseTyping = verboseTyping, _StackRef = stackRef, _NameCacheRef = nameCache, _DebuggingRef = isDebugging, _NotationDB = notationDB, _ModuleName = moduleName program })
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
                        LVar lv -> Map.lookup lv typeMap
                        _ -> Nothing
                parsePrimitiveInput :: Maybe (MonoType Int) -> String -> Maybe TermNode
                parsePrimitiveInput (Just ty)
                    | ty == mkTyNat = parseNat
                    | ty == mkTyChr = parseChr
                    | ty == mkTyList mkTyChr = parseStr
                parsePrimitiveInput _ = \src -> parseNat src `mplus` parseChr src `mplus` parseStr src
                parseNat :: String -> Maybe TermNode
                parseNat src = case reads src of
                    [(n, "")] | n >= (0 :: Integer) -> Just (mkNCon (DC_NatL n))
                    _ -> Nothing
                parseChr :: String -> Maybe TermNode
                parseChr src = case reads src of
                    [(ch, "")] -> Just (mkNCon (DC_ChrL ch))
                    _ -> Nothing
                parseStr :: String -> Maybe TermNode
                parseStr src = case reads src of
                    [(str, "")] -> Just (stringTerm str)
                    _ -> Nothing
                stringTerm :: String -> TermNode
                stringTerm = foldr cons (mkNCon DC_Nil) where
                    cons ch acc = mkNApp (mkNApp (mkNCon DC_Cons) (mkNCon (DC_ChrL ch))) acc
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
                                _ <- promptify (diagnosticNoLocWith mode "HolBETA2-REPLError" [Z.Doc.text "`:reload' is not available inside `:debug' mode or while a query is searching for answers."])
                                return ()
                            _ | (":assign " `List.isPrefixOf` response) ->
                                handleAssign env ctx (drop (length (":assign " :: String)) response)
                            _ | (":show " `List.isPrefixOf` response) -> do
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
                        _ <- promptify (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "Expected ':assign ?X := t.'."])
                        return ()
                    Just (varName, tBody) -> do
                        let stripQuests :: String -> String
                            stripQuests [] = []
                            stripQuests ('?' : cs) = stripQuests cs
                            stripQuests (c : cs) = c : stripQuests cs
                            queryStr = "?- " ++ varName ++ " = " ++ mapConToLVar (stripQuests tBody)
                        cache <- readIORef nameCache
                        result <- execUniqueT $ runExceptT (compileAssign varName queryStr)
                        case result of
                            Left err -> do
                                _ <- promptify err
                                return ()
                            Right (compiledLV, t_compiled, inferredTy, nameToType) -> do
                                let resolveDisplayName nm = case fromDisplay nm cache of
                                        Just r -> Just r
                                        Nothing -> parseAnonymousLV nm
                                    targetLV = case resolveDisplayName varName of
                                        Just resolved -> resolved
                                        Nothing -> compiledLV
                                    labelingForCheck = _CurrentLabeling ctx
                                    xconNames =
                                        [ (nm, uni)
                                        | LV_Named nm <- Set.toList (getLVars t_compiled)
                                        , Just uni <- [parseXcon nm]
                                        ]
                                    xconErrors = concat
                                        [ case IntMap.lookup uni (_ConTypes labelingForCheck) of
                                            Nothing -> ["'c_" ++ show uni ++ "' is not a known rigid constant in this state"]
                                            Just actual -> case Map.lookup nm nameToType of
                                                Nothing -> []  -- typechecker didn't constrain it; trust the runtime type
                                                Just inferred
                                                    | typeCompatible actual inferred -> []
                                                    | otherwise -> pure ("type mismatch for 'c_" ++ shows uni ("' — runtime type is " ++ showsMonoType notationDB 0 actual (", but context requires " ++ showsMonoType notationDB 0 inferred "")))
                                        | (nm, uni) <- xconNames
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
                                    mexpectedTy = Map.lookup targetLV typeMap
                                    badType = case mexpectedTy of
                                        Just expectedTy -> not (typeCompatible expectedTy inferredTy)
                                        Nothing -> False  -- anonymous targets: fall back to HOPU/kernel
                                if not (null xconErrors)
                                    then do
                                        _ <- promptify (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text (List.intercalate "; " xconErrors)])
                                        return ()
                                else if badType
                                    then do
                                        case mexpectedTy of
                                            Just expectedTy -> do
                                                _ <- promptify (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text ("Type mismatch for '" ++ varName ++ "'; expected " ++ showsMonoType notationDB 0 expectedTy (", got " ++ showsMonoType notationDB 0 inferredTy ""))])
                                                return ()
                                            Nothing -> return ()  -- unreachable
                                    else do
                                        result <- runRuntime (cmdAssign varName t_resolved) env
                                        case result of
                                            Left err -> do
                                                _ <- promptify (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text err])
                                                return ()
                                            Right () -> do
                                                composed_subst <- do
                                                    ep <- readIORef pendingSubst
                                                    return (ep <> _TotalVarBinding ctx)
                                                let t_zonked = bindVars composed_subst t_resolved
                                                    pp = prettyTerm notationDB cache
                                                _ <- promptify ("*** :assign: " ++ pp (mkLVar targetLV) (" := " ++ pp t_zonked "."))
                                                return ()
                mapConToLVar :: String -> String
                mapConToLVar = go where
                    isIdChar c = c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "_")
                    isDigitC c = c `elem` ['0' .. '9']
                    go [] = []
                    go str@(c : rest0)
                        | not (isIdChar c) = c : go rest0
                        | otherwise = case span isIdChar str of
                            (ident, rest) -> rewrite ident ++ go rest
                    rewrite ident = case ident of
                        'c' : '_' : ds | not (null ds) && all isDigitC ds -> "XCON_" ++ ds
                        _ -> ident
                parseXcon :: LargeId -> Maybe Int
                parseXcon nm = case nm of
                    'X' : 'C' : 'O' : 'N' : '_' : rest -> case reads rest of
                        [(n, "")] -> Just n
                        _ -> Nothing
                    _ -> Nothing
                typeCompatible :: MonoType Int -> MonoType Int -> Bool
                typeCompatible (TyMTV _) _ = True
                typeCompatible _ (TyMTV _) = True
                typeCompatible (TyVar _) _ = True
                typeCompatible _ (TyVar _) = True
                typeCompatible (TyCon (TCon tc1 _)) (TyCon (TCon tc2 _)) = tc1 == tc2
                typeCompatible (TyApp f1 a1) (TyApp f2 a2) = typeCompatible f1 f2 && typeCompatible a1 a2
                typeCompatible _ _ = False
                compileAssign :: MonadUnique m => String -> String -> ExceptT ErrMsg m (LogicVar, TermNode, MonoType Int, Map.Map LargeId (MonoType Int))
                compileAssign varName queryStr = case runHolLexer queryStr of
                    Left (row, col) -> throwE (diagnosticWith mode "HolBETA2-AssignError" (Just (lines queryStr)) (SLoc (row, col) (row, col)) [Z.Doc.text "Lexing failed."])
                    Right tokens -> case runHolParser tokens of
                        Left Nothing -> throwE (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "Parsing failed at EOF."])
                        Left (Just token) -> throwE (diagnosticWith mode "HolBETA2-AssignError" (Just (lines queryStr)) (getSLoc token) [Z.Doc.text "Parsing failed."])
                        Right (Right _) -> throwE (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "Expected a query, not a declaration."])
                        Right (Left termRep0) -> do
                            termRep <- case resolveTermWithFixity notationDB termRep0 of
                                Left (FixityError loc msg) -> throwE (diagnosticWith mode "HolBETA2-AssignError" (Just (lines queryStr)) loc [Z.Doc.text "Parsing failed.", Z.Doc.text msg])
                                Right termRep -> return termRep
                            (term2, free_vars) <- desugarQuery (Notation.expandTermRep expansionDB termRep)
                            (term3, (used_mtvs, assumptions)) <- checkTypeWithDiagnostic mode (Just (lines queryStr)) notationDB (_TypeDecls program) term2 mkTyO
                            term4 <- convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) term3
                            term5 <- either throwE return (installPresburger term4)
                            inferredTy <- case Map.lookup varName free_vars >>= \ivar -> Map.lookup ivar assumptions of
                                Just typ -> return typ
                                Nothing -> throwE (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "Could not infer type for the binding."])
                            let nameToType = Map.fromList [ (nm, ty) | (nm, ivar) <- Map.toList free_vars , Just ty <- [Map.lookup ivar assumptions] ]
                            case unfoldlNApp (rewrite NF term5) of
                                (NCon (DC DC_eq) _, [_typeArg, lhs, rhs]) -> case rewrite NF lhs of
                                    LVar lv -> return (lv, rhs, inferredTy, nameToType)
                                    _ -> throwE (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "LHS did not resolve to a logic variable."])
                                _ -> throwE (diagnosticNoLocWith mode "HolBETA2-AssignError" [Z.Doc.text "Did not compile to an equality."])
                printAnswer :: Context -> IO RunMore
                printAnswer ctx
                    | isShort && isClear = return False
                    | isClear && List.null theAnswerSubst = return False
                    | isClear = do
                        cache <- readIORef nameCache
                        let pp = prettyTerm notationDB cache
                        promptify "The answer substitution is:"
                        sequence_
                            [ promptify (myTabs ++ v ++ " := " ++ pp t ".")
                            | (v, t) <- theAnswerSubst
                            ]
                        askToRunMore
                    | hasGroundContradiction = return True
                    | otherwise = do
                        printDisagreements
                        askToRunMore
                    where
                        transCl :: Ord a => (a -> Set.Set a) -> a -> Set.Set a
                        transCl rel start = dfs (rel start) Set.empty where
                            dfs current visited
                                | Set.null current = visited
                                | otherwise = dfs next visited'
                                where
                                    news = current `Set.difference` visited
                                    visited' = visited `Set.union` news
                                    next = Set.unions [ rel x | x <- Set.toList news ]
                        dependOn :: LogicVar -> Set.Set LogicVar
                        dependOn x
                            = case Map.lookup x (unVarBinding (_TotalVarBinding ctx)) of
                                Nothing -> Set.empty
                                Just t -> getLVars t
                        relevants :: Set.Set LogicVar
                        relevants = Set.fromList [ LV_Named nm | nm <- nms ] `Set.union` Set.unions [ transCl dependOn (LV_Named nm) | nm <- nms ] where
                            nms = [ nm | LV_Named nm <- Set.toList (Map.keysSet (unVarBinding (_TotalVarBinding ctx))) ]
                        final_ctx :: Context
                        final_ctx = Context
                            { _TotalVarBinding = VarBinding (unVarBinding (_TotalVarBinding ctx) `Map.restrictKeys` relevants)
                            , _CurrentLabeling = _CurrentLabeling ctx
                            , _LeftConstraints = prunedConstraints
                            , _ContextThreadId = _ContextThreadId ctx
                            , _debuggindModeOn = _debuggindModeOn ctx
                            }
                        groundDropped :: [Constraint]
                        groundDropped = do
                            it <- _LeftConstraints ctx
                            case it of
                                ArithmeticConstraint b -> case evaluateB b of
                                    Right True -> []
                                    _ -> pure it
                                EvalutionConstraint lhs rhs -> case (evaluateA lhs, evaluateA rhs) of
                                    (Right x, Right y) -> if x == y then [] else pure it
                                    _ -> pure it
                                it -> pure it
                        entailmentDropped :: [Constraint]
                        entailmentDropped = go [] groundDropped where
                            go kept [] = reverse kept
                            go kept (c : rest) = case c of
                                ArithmeticConstraint t
                                    | arithEntails (otherArith kept rest) t -> go kept rest
                                _ -> go (c : kept) rest
                            otherArith :: [Constraint] -> [Constraint] -> [TermNode]
                            otherArith kept rest =
                                [ t | ArithmeticConstraint t <- kept ++ rest ]
                        prunedConstraints :: [Constraint]
                        prunedConstraints = List.sortOn (\c -> shows c "") entailmentDropped
                        theAnswerSubst :: [(LargeId, TermNode)]
                        theAnswerSubst = [ (v, bindVars (_TotalVarBinding final_ctx) t) | (LV_Named v, t) <- Map.toList (unVarBinding (eraseTrivialBinding (_TotalVarBinding final_ctx))) ]
                        isShort :: Bool
                        isShort = Set.null (getLVars query)
                        isClear :: Bool
                        isClear = List.null (_LeftConstraints final_ctx)
                        hasGroundContradiction :: Bool
                        hasGroundContradiction = any contradicts (_LeftConstraints final_ctx)
                        contradicts :: Constraint -> Bool
                        contradicts (ArithmeticConstraint b)
                            = case evaluateB b of
                                Right False -> True
                                Left "ill" -> True
                                _ -> False
                        contradicts (EvalutionConstraint lhs rhs)
                            = case (evaluateA lhs, evaluateA rhs) of
                                (Right x, Right y) -> x /= y
                                (Left "ill", _) -> True
                                (_, Left "ill") -> True
                                _ -> False
                        contradicts _ = False
                        askToRunMore :: IO RunMore
                        askToRunMore = do
                            str <- promptify "Find more solutions? [Y/n] "
                            if List.null str then askToRunMore else return (isYES str)
                        printDisagreements :: IO ()
                        printDisagreements = do
                            cache <- readIORef nameCache
                            let pp = prettyTerm notationDB cache
                            promptify "The remaining constraints are:"
                            sequence_
                                [ promptify (myTabs ++ shows constraint "")
                                | constraint <- _LeftConstraints final_ctx
                                ]
                            promptify "The binding is:"
                            sequence_
                                [ promptify (myTabs ++ pp (mkLVar v) (" := " ++ pp t "."))
                                | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))
                                ]
                        evalokay :: Bool
                        evalokay = and
                            [ case (evaluateA lhs, evaluateA rhs) of
                                (Right x, Right y) -> x == y
                                _ -> False 
                            | EvalutionConstraint lhs rhs <- _LeftConstraints final_ctx
                            ]
                        arithokay :: Bool
                        arithokay = and
                            [ case evaluateB b of
                                Right b -> b
                                _ -> False
                            | ArithmeticConstraint b <- _LeftConstraints final_ctx
                            ]
                        consistent :: Bool
                        consistent = evalokay && arithokay

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
runHol mode = do
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
                replResult <- runREPL mode (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName }) Notation.initial Notation.initialExpansionDB
                case replResult of
                    ReplQuit -> return ()
                    ReplReload -> runHol mode
            Just file_name -> runHolFile mode file_name
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
runHolFile mode file_name = do
    let my_file_dir = file_name ++ ".hol"
        myModuleName = modifySep '/' (const ".") id file_name
    msrc <- liftIO $ readFileNow my_file_dir
    case msrc of
        Nothing -> do
            liftIO $ putStrLn (diagnosticNoLocWith mode "HolBETA2-FileError" [Z.Doc.text ("Cannot read file `" ++ my_file_dir ++ "'.")])
            runHol mode
        Just _ -> do
            file_abs_dir <- fmap (fromMaybe my_file_dir) (liftIO $ makePathAbsolutely my_file_dir)
            lift $ shellyM (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", interpreted )")
            result <- loadMainWithDiagnostic mode theInitialKindDecls theInitialTypeDecls theInitialFactDecls my_file_dir
            case result of
                Left err_msg -> do
                    liftIO $ putStrLn err_msg
                    runHol mode
                Right loaded -> do
                    liftIO $ mapM_ putStrLn (loadedWarnings loaded)
                    let mainEnv = loadedMain loaded
                        program2 = Program
                            { _KindDecls  = moduleEnvKinds mainEnv
                            , _TypeDecls  = moduleEnvTypes mainEnv
                            , _FactDecls  = moduleEnvFacts mainEnv
                            , moduleName  = moduleEnvName mainEnv
                            }
                    lift $ shellyM (moduleEnvName mainEnv ++ "> Ok, one module loaded.")
                    replResult <- runREPL mode program2 (moduleEnvNotation mainEnv) (moduleEnvExpansion mainEnv)
                    case replResult of
                        ReplQuit -> return ()
                        ReplReload -> runHolFile mode file_name

mainWithModeM :: DiagnosticMode -> ShellyT ()
mainWithModeM = execUniqueT . runHol

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
