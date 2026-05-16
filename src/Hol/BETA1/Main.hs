module Hol.BETA1.Main where

import Hol.BETA1.Arith (installPresburger)
import Hol.BETA1.Compiler
import Hol.BETA1.Constant
import Hol.BETA1.Debugger
import Hol.BETA1.Desugarer
import Hol.BETA1.Header
import Hol.BETA1.HOPU
import Hol.BETA1.PlanHolLexer
import Hol.BETA1.PlanHolParser
import Hol.BETA1.Runtime
import Hol.BETA1.TermNode
import Hol.BETA1.TypeChecker
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
import Z.System
import Z.Utils
import Data.IntMap (restrictKeys)

type AnalyzerOuput = Either TermRep [DeclRep]

runAnalyzer :: String -> Either ErrMsg AnalyzerOuput
runAnalyzer src0
    = case runHolLexer src0 of
        Left (row, col) -> Left ("*** lexing error at { row = " ++ showsPrec 0 row (", col = " ++ showsPrec 0 col " }."))
        Right src1 -> case runHolParser src1 of
            Left Nothing -> Left ("*** parsing error at EOF.")
            Left (Just token) -> case getSLoc token of
                SLoc (row1, col1) (row2, col2) -> Left ("*** parsing error at { row = " ++ showsPrec 0 row1 (", col = " ++ showsPrec 0 col1 " }."))
            Right output -> Right output

isYES :: String -> Bool
isYES str = str `elem` [ str1 ++ str2 ++ str3 | str1 <- ["Y", "y"], str2 <- ["", "es"], str3 <- if null str2 then [""] else ["", "."] ]

addIndex :: [Fact] -> Map.Map Constant [Fact]
addIndex facts = Map.fromListWith (\new old -> old ++ new) [ (hd f', [f']) | f <- facts, let f' = rewrite NF f ] where
    hd :: Fact -> Constant
    hd t = case unfoldlNApp t of
        (NLam _ _ t, _) -> hd t
        (NCon (DC (DC_LO LO_ty_pi)), [t]) -> hd t
        (NCon (DC (DC_LO LO_pi)), [t]) -> hd t
        (NCon (DC (DC_LO LO_if)), [t, _]) -> hd t
        (NCon c, _) -> c

execRuntime :: RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr (UniqueT IO) Satisfied
execRuntime env isDebugging facts query = do
    call_id <- getUnique
    -- §3.4 CMTT: seed `_NamedTypes` with the typechecker's inferences
    -- for `LV_Named` query variables so HOPU's `lookupLVarType` covers
    -- them uniformly with `_VarTypes`. `_TypeEnv` stashes the program's
    -- declared-constant types so HOPU's `typeOfTerm` resolves DC_Named
    -- (and DC_LO/arithmetic) constants without re-plumbing TypeEnv.
    let namedTypes = Map.fromList [ (nm, ty) | (LV_Named nm, ty) <- Map.toList (_TypeInfo env) ]
        initialLabeling = Labeling
            { _ConLabel = IntMap.empty
            , _VarLabel = IntMap.empty
            , _ConTypes = IntMap.empty
            , _VarTypes = IntMap.empty
            , _NamedTypes = namedTypes
            , _TyVarKeys = IntMap.empty
            , _TypeEnv = _ProgramTypeEnv env
            }
        initialContext = Context { _TotalVarBinding = mempty, _CurrentLabeling = initialLabeling, _LeftConstraints = [], _ContextThreadId = call_id, _debuggindModeOn = isDebugging }
    runTransition env (getLVars query) [(initialContext, [Cell { _GivenFacts = addIndex facts, _GivenHypos = [], _ScopeLevel = 0, _WantedGoal = query, _CellCallId = call_id }])]

runREPL :: Program TermNode -> UniqueT IO ()
runREPL program = do
    isDebugging <- lift (newIORef False)
    verboseTyping <- lift (newIORef False)
    nameCache <- lift (newIORef initialCache)
    go isDebugging verboseTyping nameCache
  where
    myTabs :: String
    myTabs = ""
    promptify :: String -> IO String
    promptify str = shelly (moduleName program ++ "> " ++ str)
    mkRuntimeEnv :: IORef Debugging -> IORef Bool -> IORef NameCache -> IORef LogicVarSubst -> Map.Map LogicVar (MonoType Int) -> TermNode -> IO RuntimeEnv
    mkRuntimeEnv isDebugging verboseTyping nameCache pendingSubst typeMap query = do
        stackRef <- newIORef []
        return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer, _TypeInfo = typeMap, _PendingSubst = pendingSubst, _ProgramTypeEnv = _TypeDecls program, _VerboseTyping = verboseTyping, _StackRef = stackRef, _NameCacheRef = nameCache, _DebuggingRef = isDebugging })
      where
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
        -- §3.2 `:assign ?V := t.` parsing: strip the literal `?` from the
        -- variable name and split on ` := `. The body is re-assembled as
        -- the ordinary query `?- V = t.` so the existing lex+parse+desugar
        -- +typecheck+convert pipeline does the heavy lifting (including
        -- type-coherence: `DC_eq : forall A. A -> A -> o` forces `V`'s
        -- inferred type and `t`'s inferred type to unify).
        parseAssign :: String -> Maybe (String, String)
        parseAssign body0 =
            let body = dropWhile (== ' ') body0
            in case body of
                '?' : rest -> findSep rest ""
                _ -> Nothing
          where
            findSep :: String -> String -> Maybe (String, String)
            findSep [] _ = Nothing
            findSep (' ' : ':' : '=' : ' ' : rs) acc =
                Just (reverse (dropWhile (== ' ') acc), dropWhile (== ' ') rs)
            findSep (c : cs) acc = findSep cs (c : acc)
        handleAssign :: RuntimeEnv -> Context -> String -> IO ()
        handleAssign env ctx body = case parseAssign body of
            Nothing -> do
                _ <- promptify "*** :assign error: expected ':assign ?X := t.'"
                return ()
            Just (varName, tBody) -> do
                -- §3.2.2: the user may reference other flexible variables
                -- inside `t` (e.g. `:assign ?F := ?V_17.`). Both the
                -- viewer's `?V_<n>` display and `LV_Named` user variables
                -- carry a literal `?` only in front of the *single*
                -- variable name. We strip every `?` that immediately
                -- precedes an identifier character so that the synthetic
                -- query `?- X = ...` lexes cleanly; `nameSwap` below
                -- restores the resolved LogicVar for each such name.
                let stripQuests :: String -> String
                    stripQuests [] = []
                    stripQuests ('?' : cs) = stripQuests cs
                    stripQuests (c : cs) = c : stripQuests cs
                    -- §3.4 CMTT: rigid constants introduced by pi/sigma
                    -- have viewer name `c_<n>`. The lexer treats `c_<n>`
                    -- as a `DC_Named` constant (lowercase head), and the
                    -- typechecker rejects unknown names. We pre-rename
                    -- `c_<n>` → `XCON_<n>` so it parses as an LV_Named
                    -- (uppercase head), then post-substitute the actual
                    -- DC_Unique back in. `XCON_` is unlikely to collide
                    -- with real user variable names.
                    queryStr = "?- " ++ varName ++ " = " ++ mapConToLVar (stripQuests tBody)
                cache <- readIORef nameCache
                result <- execUniqueT $ runExceptT (compileAssign varName queryStr)
                case result of
                    Left err -> do
                        _ <- promptify err
                        return ()
                    Right (compiledLV, t_compiled, inferredTy, nameToType) -> do
                        -- §3.5: resolve user-input display names back to the
                        -- real LogicVar each refers to. If a name is in
                        -- `NameCache.fromDisplay`, the user *meant* that
                        -- anonymous variable (LV_Unique/LV_ty_var); the
                        -- compiler had to produce a fresh `LV_Named` because
                        -- it has no knowledge of the cache. We patch this up
                        -- on both sides:
                        --   • `targetLV` — the LHS the user typed
                        --   • `nameSwap` — every other LV_Named appearing in
                        --     `t_compiled` whose name happens to be a cached
                        --     display name (the user can refer to anonymous
                        --     variables anywhere inside `t`).
                        let resolveDisplayName :: String -> Maybe LogicVar
                            resolveDisplayName nm = case fromDisplay nm cache of
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
                            -- Validate each `XCON_<n>` placeholder: the
                            -- referenced rigid constant must (i) exist in
                            -- the current `_ConTypes` and (ii) carry a
                            -- type compatible with what the typechecker
                            -- inferred for that position.
                            xconErrors = concat
                                [ case IntMap.lookup uni (_ConTypes labelingForCheck) of
                                    Nothing -> ["'c_" ++ show uni ++ "' is not a known rigid constant in this state"]
                                    Just actual -> case Map.lookup nm nameToType of
                                        Nothing -> []  -- typechecker didn't constrain it; trust the runtime type
                                        Just inferred
                                            | typeCompatible actual inferred -> []
                                            | otherwise -> ["type mismatch for 'c_" ++ show uni
                                                    ++ "' — runtime type is " ++ showsMonoType 0 actual
                                                        (", but context requires " ++ showsMonoType 0 inferred "")]
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
                                _ <- promptify ("*** :assign error: " ++ List.intercalate "; " xconErrors)
                                return ()
                          else if badType
                            then case mexpectedTy of
                                Just expectedTy -> do
                                    _ <- promptify ("*** :assign error: type mismatch for '" ++ varName ++ "' — expected " ++ showsMonoType 0 expectedTy (", got " ++ showsMonoType 0 inferredTy ""))
                                    return ()
                                Nothing -> return ()  -- unreachable
                            else do
                                -- §4.4.2: hand off to the library API. cmdAssign owns
                                -- the snapshot/restore, occurs check, scope check,
                                -- and the (T4) consistency check. We retain the
                                -- caller-side type check above (since cmdAssign's
                                -- signature deliberately takes an already-checked
                                -- TermNode), and render the success message here
                                -- because cmdAssign returns just `Right ()`.
                                result <- runRuntime (cmdAssign varName t_resolved) env
                                case result of
                                    Left err -> do
                                        _ <- promptify ("*** :assign error: " ++ err)
                                        return ()
                                    Right () -> do
                                        composed_subst <- do
                                            ep <- readIORef pendingSubst
                                            return (ep <> _TotalVarBinding ctx)
                                        let t_zonked = bindVars composed_subst t_resolved
                                            pp = prettyTerm cache
                                        _ <- promptify ("*** :assign: " ++ pp (mkLVar targetLV) (" := " ++ pp t_zonked "."))
                                        return ()
        -- §3.4 CMTT: rewrite each `c_<digits>` identifier in a `:assign`
        -- input string to `XCON_<digits>` so the lexer/parser treats it
        -- as an LV_Named placeholder (uppercase head). After compilation
        -- those placeholders are swapped for the actual `DC_Unique`.
        -- Identifier boundaries are detected by `isIdChar` so we don't
        -- mangle the middle of unrelated tokens.
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
        -- Inverse of `mapConToLVar`'s renaming: a `LargeId` of the form
        -- `XCON_<digits>` is a placeholder for `DC_Unique (Unique n)`.
        -- Returns `Just n` on match, `Nothing` otherwise.
        parseXcon :: LargeId -> Maybe Int
        parseXcon nm = case nm of
            'X' : 'C' : 'O' : 'N' : '_' : rest -> case reads rest of
                [(n, "")] -> Just n
                _ -> Nothing
            _ -> Nothing
        -- Structural compatibility: `TyMTV` (unresolved metatype variable)
        -- and `TyVar` (rigid type parameter introduced by `Forall`) are
        -- treated as wildcards on either side; everything else must agree
        -- pointwise. This is conservative — it admits anything the real
        -- HOPU layer would have accepted, and rejects obviously
        -- incompatible shapes (function vs. nat) before the propagation
        -- so the user gets a focused error rather than a silent failure.
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
            Left _ -> throwE "*** :assign error: lex failed"
            Right tokens -> case runHolParser tokens of
                Left _ -> throwE "*** :assign error: parse failed"
                Right (Right _) -> throwE "*** :assign error: expected a query, not a declaration"
                Right (Left termRep) -> do
                    (term2, free_vars) <- desugarQuery termRep
                    (term3, (used_mtvs, assumptions)) <- checkType (_TypeDecls program) term2 mkTyO
                    term4 <- convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) term3
                    term5 <- either throwE return (installPresburger term4)
                    -- The inferred type of `X` inside the synthetic query
                    -- `?- X = t.` is recovered via `free_vars[varName] -> IVar`
                    -- then `assumptions[IVar] -> MonoType Int`. `DC_eq`
                    -- forces both sides to share that type, so this is
                    -- also the inferred type of `t`.
                    inferredTy <- case Map.lookup varName free_vars >>= \ivar -> Map.lookup ivar assumptions of
                        Just typ -> return typ
                        Nothing -> throwE "*** :assign error: could not infer type for the binding"
                    -- The same lookup, but flipped to a (LargeId -> MonoType)
                    -- map covering every free name in the synthetic query.
                    -- Used by `handleAssign` to type-check `XCON_<n>`
                    -- placeholders against the runtime's `_ConTypes`.
                    let nameToType = Map.fromList
                            [ (nm, ty)
                            | (nm, ivar) <- Map.toList free_vars
                            , Just ty <- [Map.lookup ivar assumptions]
                            ]
                    case unfoldlNApp (rewrite NF term5) of
                        (NCon (DC DC_eq), [_typeArg, lhs, rhs]) -> case rewrite NF lhs of
                            LVar lv -> return (lv, rhs, inferredTy, nameToType)
                            _ -> throwE "*** :assign error: LHS did not resolve to a logic variable"
                        _ -> throwE "*** :assign error: did not compile to an equality"
        printAnswer :: Context -> IO RunMore
        printAnswer ctx
            | isShort && isClear = return False
            | isClear && List.null theAnswerSubst = return False
            | isClear = do
                cache <- readIORef nameCache
                let pp = prettyTerm cache
                promptify "The answer substitution is:"
                sequence_
                    [ promptify (myTabs ++ v ++ " := " ++ pp t ".")
                    | (v, t) <- theAnswerSubst
                    ]
                askToRunMore
            | not consistent = return True
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
                    , _LeftConstraints = do
                        it <- _LeftConstraints ctx
                        case it of
                            ArithmeticConstraint b -> case evaluateB b of
                                Right True -> []
                                _ -> pure it
                            EvalutionConstraint lhs rhs -> case (evaluateA lhs, evaluateA rhs) of
                                (Right x, Right y) -> if x == y then [] else pure it
                                _ -> pure it
                            it -> pure it
                    , _ContextThreadId = _ContextThreadId ctx
                    , _debuggindModeOn = _debuggindModeOn ctx
                    }
                theAnswerSubst :: [(LargeId, TermNode)]
                -- §3.2.4: after `:assign ?V_n := t.`, the kernel ctx holds
                -- both `?V_n := t` and any HOPU-derived `F := ?V_n`. The
                -- naive `eraseTrivialBinding` only normalises *trivial*
                -- LV-to-LV pairs and won't follow `F → ?V_n → t`. We zonk
                -- each RHS through the full ctx binding once so the user
                -- sees the resolved value rather than the indirected one.
                theAnswerSubst = [ (v, bindVars (_TotalVarBinding final_ctx) t) | (LV_Named v, t) <- Map.toList (unVarBinding (eraseTrivialBinding (_TotalVarBinding final_ctx))) ]
                isShort :: Bool
                isShort = Set.null (getLVars query)
                isClear :: Bool
                isClear = List.null (_LeftConstraints final_ctx)
                askToRunMore :: IO RunMore
                askToRunMore = do
                    str <- promptify "Find more solutions? [Y/n] "
                    if List.null str then askToRunMore else return (isYES str)
                printDisagreements :: IO ()
                printDisagreements = do
                    cache <- readIORef nameCache
                    let pp = prettyTerm cache
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
    go :: IORef Debugging -> IORef Bool -> IORef NameCache -> UniqueT IO ()
    go isDebugging verboseTyping nameCache = do
        query <- lift $ promptify ""
        case query of
            "" -> do
                lift $ shelly "Hol >>= quit"
                return ()
            ":q" -> do
                lift $ shelly "Hol >>= quit"
                return ()
            ":d" -> do
                lift $ do
                    modifyIORef isDebugging not
                    debugging <- readIORef isDebugging
                    promptify ("Debugging mode " ++ (if debugging then "on" else "off") ++ ".")
                go isDebugging verboseTyping nameCache
            ":short" -> do
                lift $ do
                    writeIORef verboseTyping False
                    promptify "Typing display: short."
                go isDebugging verboseTyping nameCache
            ":verbose" -> do
                lift $ do
                    writeIORef verboseTyping True
                    promptify "Typing display: verbose."
                go isDebugging verboseTyping nameCache
            query0 -> case runAnalyzer query0 of
                Left err_msg -> do
                    lift $ putStrLn err_msg
                    go isDebugging verboseTyping nameCache
                Right output -> case output of
                    Left query1 -> do
                        result <- runExceptT $ do
                            (query2, free_vars) <- desugarQuery query1
                            (query3, (used_mtvs, assumptions)) <- checkType (_TypeDecls program) query2 mkTyO
                            query4 <- convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) query3
                            query5 <- either throwE return (installPresburger query4)
                            -- §3.4: the debugger lists every visible flexible
                            -- variable with its inferred type. The query
                            -- type-checker is the only point in the pipeline
                            -- that *knows* these types — `assumptions` carries
                            -- (IVar -> MonoType Int) and `free_vars` maps each
                            -- user-visible `LargeId` to its IVar. We lift both
                            -- to `LogicVar`-keyed form so the runtime can hand
                            -- the data to `showsCurrentState` without ever
                            -- looking back through compilation state.
                            let typeMap = Map.fromList
                                    [ (LV_Named name, typ)
                                    | (name, ivar) <- Map.toList free_vars
                                    , Just typ <- [Map.lookup ivar assumptions]
                                    ]
                            return (query5, typeMap)
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                go isDebugging verboseTyping nameCache
                            Right (query4, typeMap) -> do
                                pendingSubst <- lift $ newIORef (VarBinding Map.empty)
                                runtime_env <- lift $ mkRuntimeEnv isDebugging verboseTyping nameCache pendingSubst typeMap query4
                                answer <- runExceptT (execRuntime runtime_env isDebugging (_FactDecls program) query4)
                                case answer of
                                    Left runtime_err -> case runtime_err of
                                        BadGoalGiven _ -> lift $ putStrLn "*** runtime-error: bad goal given!"
                                        BadFactGiven _ -> lift $ putStrLn "*** runtime-error: bad fact given!"
                                    Right sat -> do
                                        lift $ promptify (if sat then "yes." else "no.")
                                        return ()
                                go isDebugging verboseTyping nameCache
                    Right src1 -> do
                        lift $ putStrLn "*** parsing-error: it is not a query."
                        go isDebugging verboseTyping nameCache

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
    ]

theInitialFactDecls :: [TermNode]
theInitialFactDecls = [eqFact] where
    -- §3.4 CMTT: the outer `ty_pi` binder carries `TyMTV mtv_eq` in
    -- its LamType marker slot (matching `Compiler.makeUniversalClosure`'s
    -- convention for compiled facts). The inner `pi (x : A)` reuses the
    -- same MTV key so `Runtime.instantiateFact` rewrites both occurrences
    -- to the same fresh `LV_ty_var` when peeling the outer binder.
    -- A negative `Unique` is safe: `getUnique` only mints non-negative
    -- IDs, so this key never collides with a runtime-allocated MTV.
    mtv_eq :: MetaTVar
    mtv_eq = Unique (-1)
    eqFact :: TermNode
    eqFact = mkNApp (mkNCon LO_ty_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv_eq)) (mkNApp (mkNCon LO_pi) (mkNLamHintTy Nothing (mkLamType (TyMTV mtv_eq)) (mkNApp (mkNApp (mkNApp (mkNCon DC_eq) (mkNIdx 1)) (mkNIdx 0)) (mkNIdx 0)))))

theDefaultModuleName :: String
theDefaultModuleName = "Hol"

runHol :: UniqueT IO ()
runHol = do
    consistency_ptr <- lift $ newIORef ""
    file_dir <- lift $ shelly "Hol =<< "
    maybe_file_name <- case matchFileDirWithExtension file_dir of
        ("", "") -> return Nothing
        (file_name, ".hol") -> return (Just file_name)
        (file_name, "") -> return (Just file_name)
        (file_name, '.' : wrong_extension) -> do
            lift $ writeIORef consistency_ptr (theDefaultModuleName ++ "> " ++ shows wrong_extension " is a non-executable file extension.")
            return Nothing
    consistency <- lift $ readIORef consistency_ptr
    case consistency of
        "" -> case maybe_file_name of
            Nothing -> do
                lift $ shelly (theDefaultModuleName ++ "> Ok, no module loaded.")
                runREPL (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName })
            Just file_name -> do
                let my_file_dir = file_name ++ ".hol"
                    myModuleName = modifySep '/' (const ".") id file_name
                src <- lift $ readFile my_file_dir
                file_abs_dir <- fmap (fromMaybe my_file_dir) (lift $ makePathAbsolutely my_file_dir)
                lift $ shelly (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", interpreted )")
                case runAnalyzer src of
                    Left err_msg -> do
                        lift $ putStrLn err_msg
                        runHol
                    Right output -> case output of
                        Left query1 -> do
                            lift $ putStrLn "*** parsing-error: it is not a program."
                            runHol
                        Right program1 -> do
                            result <- runExceptT $ do
                                module1 <- desugarProgram theInitialKindDecls theInitialTypeDecls theDefaultModuleName program1
                                facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                                facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                                facts4 <- sequence [ either throwE return (installPresburger f) | f <- facts3 ]
                                return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = theInitialFactDecls ++ facts4, moduleName = myModuleName })
                            case result of
                                Left err_msg -> do
                                    lift $ putStrLn err_msg
                                    runHol
                                Right program2 -> do
                                    lift $ shelly (myModuleName ++ "> Ok, one module loaded.")
                                    runREPL program2
        inconsistent_proof -> do
            lift $ shelly inconsistent_proof
            lift $ shelly ("Hol >>= quit")
            return ()

main :: IO ()
main = execUniqueT runHol
