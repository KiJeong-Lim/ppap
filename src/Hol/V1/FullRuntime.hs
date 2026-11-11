module Hol.V1.FullRuntime where

import qualified Calc.Presburger.Internal as P
import Control.Exception (IOException, bracket, bracketOnError, onException, try)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Char (chr, ord)
import Data.Int
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Word
import Hol.BETA.Arith (ArithStore)
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime hiding (Snapshot, snapshot, restore)
import Hol.BETA.TermNode
import Hol.V1.FullBytecode
import Hol.V1.FullCompiler
import qualified Hol.V1.Services as Services
import qualified X.HigherMachine as Native
import Z.Utils

-- A session is used sequentially. Native snapshots retain immutable host-state
-- tokens; the token tables and identity/display caches grow monotonically.
data Session
    = Session
        { sessionMachine :: Native.Machine
        , sessionProgram :: FullProgram
        , sessionEnvironment :: RuntimeEnv
        , sessionDebugging :: IORef Bool
        , sessionBridge :: IORef Bridge
        , sessionConstraints :: IORef (Map.Map Word64 [Constraint])
        , sessionPremises :: IORef (Map.Map Word64 ArithStore)
        , sessionNextToken :: IORef Word64
        , sessionStopped :: IORef Bool
        }
    deriving ()

data Bridge
    = Bridge
        { bridgeVariables :: Map.Map Word64 LogicVar
        , bridgeVariableWires :: Map.Map LogicVar [Int64]
        , bridgeConstants :: Map.Map Word64 Constant
        , bridgeConstantWires :: Map.Map Constant [Int64]
        , bridgeSymbols :: IntMap.IntMap FullSymbol
        , bridgeSymbolIndices :: Map.Map String Int
        , bridgeLabeling :: Labeling
        , bridgeTypeBinders :: Map.Map MetaTVar MetaTVar
        , bridgeIdentities :: Map.Map Word64 Unique
        , bridgeIdentityBlocks :: Map.Map Word64 UniqueBlock
        , bridgeNextIdentity :: Word64
        , bridgeQuerySlots :: Word64
        , bridgeUncertain :: Bool
        }
    deriving ()

data Snapshot
    = Snapshot
        { nativeSnapshot :: Native.Snapshot
        , snapshotPending :: VarBinding
        , snapshotNames :: NameCache
        , snapshotStopped :: Bool
        }
    deriving ()

createSession :: RuntimeEnv -> IORef Bool -> FullProgram -> IO Session
createSession env debugging program = do
    either (ioError . userError) return (validateFullBytecode program)
    bracketOnError (Native.createMachine (fullWords program)) Native.closeMachine $ \machine -> do
        let slots = case fullSections (fullWords program) of
                Right (_, rows, _, _, _, _) -> rows
                Left _ -> []
            indices = Map.fromList [(symbolIdentity symbol, index) | (index, symbol) <- IntMap.toList (fullSymbols program)]
        openSession env debugging machine program slots indices 0

-- The machine runs the query of `program`. Its query variables have the
-- identities from `base` on, and `indices` finds a symbol by its identity.
openSession :: RuntimeEnv -> IORef Bool -> Native.Machine -> FullProgram -> [[Int64]] -> Map.Map String Int -> Word64 -> IO Session
openSession env debugging machine program slots indices base = do
    let labeling = Labeling IntMap.empty IntMap.empty IntMap.empty IntMap.empty (Map.fromList [(name, ty) | (LV_Named name, ty) <- Map.toList (_TypeInfo env)]) IntMap.empty (_ProgramTypeEnv env)
        variables = Map.fromList (zip [base ..] (fullVariables program))
        wires = Map.fromList [(variable, [0, fromIntegral uid, 0, isType, meta]) | (uid, (variable, [isType, meta])) <- zip [base ..] (zip (fullVariables program) slots)]
        frontier = base + fromIntegral (length (fullVariables program))
        bridge = Bridge variables wires Map.empty Map.empty (fullSymbols program) indices (labelingWithRuntimeTypes env labeling) Map.empty Map.empty Map.empty frontier frontier False
        protected = env
            { _PrintPrimitive = \ctx term -> _PrintPrimitive env ctx term `onException` Native.closeMachine machine
            , _ReadPrimitive = \ctx term -> _ReadPrimitive env ctx term `onException` Native.closeMachine machine
            }
    Session machine program protected debugging <$> newIORef bridge <*> newIORef (Map.singleton 0 []) <*> newIORef (Map.singleton 0 emptyArithStore) <*> newIORef 1 <*> newIORef False

-- A machine that keeps its program: the facts given to it stay loaded, and
-- every query runs on them. It is used by one caller at a time.
data Engine
    = Engine
        { engineMachine :: Native.Machine
        , engineProgram :: IORef LoadedTables
        }
    deriving ()

createEngine :: PreparedProgram -> IO (Either String Engine)
createEngine prepared = case loadPreparedProgram prepared >>= \loaded -> validateFullBytecode (fst loaded) >> return loaded of
    Left message -> return (Left message)
    Right (program, tables) -> bracketOnError (Native.createMachine (fullWords program)) Native.closeMachine $ \machine -> do
        ready <- Native.leaveRun machine
        case ready of
            Left message -> Native.closeMachine machine >> return (Left message)
            Right () -> Right . Engine machine <$> newIORef tables

closeEngine :: Engine -> IO ()
closeEngine = Native.closeMachine . engineMachine

-- The facts have no logic variable. A failure of the machine leaves the engine
-- unusable; a fact that does not compile leaves it as it was.
extendEngine :: Engine -> [TermNode] -> IO (Either String ())
extendEngine engine facts = do
    tables <- readIORef (engineProgram engine)
    case extendLoadedProgram tables facts >>= \extended -> validateLoadedFragment tables (fst extended) >> return extended of
        Left message -> return (Left message)
        Right (program, next) -> do
            loaded <- Native.extendProgram (engineMachine engine) (fullWords program)
            either (return . Left) (\() -> Right () <$ writeIORef (engineProgram engine) next) loaded

-- Runs a query on the program of the engine. The session is valid inside the
-- action only: the next query, extension or leaveEngine ends its run.
withQuery :: RuntimeEnv -> IORef Bool -> Engine -> Map.Map LogicVar (MonoType Int) -> TermNode -> (Session -> IO a) -> IO (Either String a)
withQuery env debugging engine queryTypes query action = do
    tables <- readIORef (engineProgram engine)
    case queryLoadedProgram tables queryTypes query >>= \program -> validateLoadedFragment tables program >> return program of
        Left message -> return (Left message)
        Right program -> do
            started <- Native.startQuery machine (fullWords program)
            frontier <- Native.uidFrontier machine
            case started >> frontier of
                Left message -> return (Left message)
                Right next -> do
                    let count = length (fullVariables program)
                    session <- openSession env debugging machine program (pairs (take (2 * count) (drop 8 (fullWords program)))) (fragmentIndices tables program) (next - fromIntegral count)
                    Right <$> action session
    where
        machine = engineMachine engine
        pairs (isType : meta : rest) = [isType, meta] : pairs rest
        pairs _ = []

-- Ends the run of the last query and releases what it allocated. A failure
-- means that the engine is unusable.
leaveEngine :: Engine -> IO (Either String ())
leaveEngine = Native.leaveRun . engineMachine

closeSession :: Session -> IO ()
closeSession = Native.closeMachine . sessionMachine

withSession :: RuntimeEnv -> IORef Bool -> FullProgram -> (Session -> IO a) -> IO a
withSession env debugging program = bracket (createSession env debugging program) closeSession

setWorkLimit :: Session -> Word64 -> IO (Either String ())
setWorkLimit session = Native.setWorkLimit (sessionMachine session)

getWorkLimit :: Session -> IO (Either String Word64)
getWorkLimit = Native.getWorkLimit . sessionMachine

takeSnapshot :: Session -> IO (Either String Snapshot)
takeSnapshot session = do
    captured <- Native.takeSnapshot (sessionMachine session)
    pending <- readIORef (_PendingSubst (sessionEnvironment session))
    names <- readIORef (_NameCacheRef (sessionEnvironment session))
    stopped <- readIORef (sessionStopped session)
    return ((\native -> Snapshot native pending names stopped) <$> captured)

restoreSnapshot :: Session -> Snapshot -> IO (Either String ())
restoreSnapshot session saved = do
    restored <- Native.restoreSnapshot (sessionMachine session) (nativeSnapshot saved)
    case restored of
        Left message -> return (Left message)
        Right () -> do
            let env = sessionEnvironment session
            writeIORef (_PendingSubst env) (snapshotPending saved)
            modifyIORef' (_NameCacheRef env) (mergeKeepingNewEntries (snapshotNames saved))
            writeIORef (sessionStopped session) (snapshotStopped saved)
            return (Right ())

closeSnapshot :: Snapshot -> IO ()
closeSnapshot = Native.closeSnapshot . nativeSnapshot

runFullProgram :: UniqueM m => RuntimeEnv -> IORef Bool -> FullProgram -> ExceptT KernelErr m Satisfied
runFullProgram env debugging program = do
    opened <- liftIO (try (createSession env debugging program) :: IO (Either IOException Session))
    session <- either (throwE . BackendError . show) return opened
    outcome <- lift (runExceptT (loop session))
    liftIO (closeSession session)
    either throwE return outcome
    where
        loop session = do
            answer <- nextSolution session
            case answer of
                Nothing -> return False
                Just ctx -> do
                    more <- liftIO (_Answer env ctx `onException` closeSession session)
                    if more then loop session else return True

nativeResult :: Monad m => Either String a -> ExceptT KernelErr m a
nativeResult = either (throwE . BackendError) return

nextSolution :: UniqueM m => Session -> ExceptT KernelErr m (Maybe Context)
nextSolution session = do
    stopped <- liftIO (readIORef (sessionStopped session))
    if stopped then return Nothing else nextSolutionActive session

nextSolutionActive :: UniqueM m => Session -> ExceptT KernelErr m (Maybe Context)
nextSolutionActive session = do
    applyPending session
    debugging <- liftIO (readIORef (sessionDebugging session))
    liftIO (Native.setDebugging machine debugging) >>= nativeResult
    result <- liftIO (Native.nextEvent machine `onException` closeSession session) >>= nativeResult
    case result of
        Native.Exhausted -> do
            liftIO (writeIORef (_StackRef env) [])
            return Nothing
        Native.Answer token _ _ -> do
            reserveIdentities session
            pending <- fetched session Native.pendingCount
            (binding, disagreements) <- if debugging || token /= 0 || pending /= 0 then completeState session else do
                reduced <- rootState session True (return ())
                maybe (completeState session) (return . fst) reduced
            ctx <- currentContext session token 0 binding disagreements
            liftIO (writeIORef (_StackRef env) [(ctx, [])])
            return (Just ctx)
        Native.Request request
            | Native.requestKind request == 4 -> do
                reserveIdentities session
                (binding, disagreements, _, cells) <- completeRequest session request
                ctx <- currentContext session (Native.requestHostState request) (Native.requestCallId request) binding disagreements
                continue <- debugInteraction session ctx cells
                if continue then do
                    applyPending session
                    liftIO (Native.resume machine 1 (Native.requestHostState request) (Native.requestPremises request) [0]) >>= nativeResult
                    nextSolution session
                else do
                    liftIO (Native.resume machine 0 (Native.requestHostState request) (Native.requestPremises request) [0]) >>= nativeResult
                    liftIO (writeIORef (sessionStopped session) True)
                    return Nothing
            | otherwise -> do
                reserveIdentities session
                (binding, disagreements, roots) <- requestState debugging request
                ctx <- currentContext session (Native.requestHostState request) (Native.requestCallId request) binding disagreements
                premises <- lookupToken "arithmetic premise" (sessionPremises session) (Native.requestPremises request)
                reply <- dispatch request roots premises ctx
                installReply session request ctx reply
                nextSolution session
    where
        machine = sessionMachine session
        env = sessionEnvironment session
        -- An antecedent contributes premises from its own term, and an
        -- equality that mentions no arithmetic is left to the native search:
        -- neither reply consults a binding, a label or a disagreement.
        requestState debugging request = case Native.requestKind request of
            3 -> termsOnly
            5 -> do
                (_, _, roots) <- termsOnly
                case roots of
                    [goal]
                        | not (Services.equalityUsesArithmetic (snd (unfoldlNApp goal))) -> return (mempty, [], roots)
                    _ -> stateWithRoots
            _ -> stateWithRoots
            where
                reducible = not debugging && Native.requestHostState request == 0 && Native.requestPremises request == 0
                termsOnly = do
                    resetLabeling session
                    roots <- decodeRoots session (Native.requestTerms request)
                    return (mempty, [], roots)
                stateWithRoots = if reducible then rootState session False (decodeRoots session (Native.requestTerms request)) >>= maybe complete (\((binding, disagreements), roots) -> return (binding, disagreements, roots)) else complete
                complete = (\(binding, disagreements, roots, _) -> (binding, disagreements, roots)) <$> completeRequest session request
        dispatch request roots premises ctx = case (Native.requestKind request, roots) of
            (2, []) -> Services.runService env premises ctx Services.Settle
            (3, [fact]) -> Services.runService env premises ctx (Services.AssumePremises fact)
            (5, [goal]) -> do
                let args = snd (unfoldlNApp goal)
                defined <- Services.runService env premises ctx (Services.EqualityDefinitions args)
                case defined of
                    Services.ServiceContinue next active -> Services.runService env active next (Services.EqualityDecision args)
                    Services.ServiceFailure -> return Services.ServiceReject
                    other -> return other
            (1, [goal]) -> case unfoldlNApp goal of
                (NCon (DC (DC_LO LO_is)) _, [lhs, rhs]) -> Services.runService env premises ctx (Services.Evaluate lhs rhs)
                (NCon (DC (DC_LO LO_debug)) _, [label]) -> Services.runService env premises ctx (Services.Debug label)
                (NCon (DC (DC_Named "print")) _, args) -> Services.runService env premises ctx (Services.Print args)
                (NCon (DC (DC_Named "read")) _, args) -> Services.runService env premises ctx (Services.Read args)
                (NCon predicate _, args) -> withExceptT (goalLocation ctx goal) (Services.runService env premises ctx (Services.Compare predicate args))
                (NPresburgerCheck rep freeOf _, []) -> Services.runService env premises ctx (Services.Presburger rep freeOf)
                _ -> throwE (BadGoalGiven goal)
            _ -> throwE (BackendError "invalid native service request")
        goalLocation ctx goal failure
            | _QueryCallId env == Just (_ContextThreadId ctx)
            , Just location <- getNodeSLoc goal
            , UnsupportedArithmeticConstraint (NApp function argument _) <- failure
            = UnsupportedArithmeticConstraint (NApp function argument (Just location))
            | otherwise = failure

fetched :: MonadIO m => Session -> (Native.Machine -> IO (Either String a)) -> ExceptT KernelErr m a
fetched session fetch = liftIO (fetch (sessionMachine session)) >>= nativeResult

-- The complete state: every native variable with its value, the event terms,
-- and the frames of a debugger stop or the declarations of any other stop.
completeState :: UniqueM m => Session -> ExceptT KernelErr m (VarBinding, [Disagreement])
completeState session = fetched session Native.fetchState >>= decodeState session

completeRequest :: UniqueM m => Session -> Native.NativeRequest -> ExceptT KernelErr m (VarBinding, [Disagreement], [TermNode], [Cell])
completeRequest session request = do
    let debug = Native.requestKind request == 4
    state <- fetched session Native.fetchState
    frames <- if debug then fetched session Native.fetchFrames else return [0]
    declarations <- if debug then return [0] else fetched session Native.fetchDeclarations
    (binding, disagreements) <- decodeState session state
    roots <- decodeRoots session (Native.requestTerms request)
    cells <- decodeFrames session frames
    void (decodeRoots session declarations)
    return (binding, disagreements, roots, cells)

-- The state a stop can consult while the host holds no constraint and no
-- premise: the query variables of an answer, the disagreements, and whatever
-- the given action decodes. Nothing is returned when a decoded variable has a
-- type that the complete state could decide differently.
rootState :: UniqueM m => Session -> Bool -> ExceptT KernelErr m a -> ExceptT KernelErr m (Maybe ((VarBinding, [Disagreement]), a))
rootState session query decodeMore = do
    state <- fetched session (\machine -> Native.fetchRootState machine query)
    decoded <- decodeState session state
    more <- decodeMore
    bridge <- liftIO (readIORef (sessionBridge session))
    return (if bridgeUncertain bridge then Nothing else Just (decoded, more))

-- Native identities are numbered in creation order at every stop, whether or
-- not the stop decodes them, before the host allocates identities of its own.
reserveIdentities :: UniqueM m => Session -> ExceptT KernelErr m ()
reserveIdentities session = do
    frontier <- fetched session Native.uidFrontier
    bridge <- liftIO (readIORef (sessionBridge session))
    let start = bridgeNextIdentity bridge
        count = toInteger frontier - toInteger start
    when (count > 0) $ do
        when (count > toInteger (maxBound :: Int)) (throwE (BackendError "native identity reservation exceeds host range"))
        reserved <- getUniqueBlock (fromInteger count)
        block <- maybe (throwE (BackendError "native identity reservation exhausted")) return reserved
        liftIO (modifyIORef' (sessionBridge session) (\current -> current { bridgeIdentityBlocks = Map.insert start block (bridgeIdentityBlocks current), bridgeNextIdentity = frontier }))

resetLabeling :: MonadIO m => Session -> m ()
resetLabeling session = liftIO (modifyIORef' (sessionBridge session) (\bridge -> bridge { bridgeLabeling = labelingWithRuntimeTypes env empty, bridgeTypeBinders = Map.empty, bridgeUncertain = False })) where
    env = sessionEnvironment session
    empty = Labeling IntMap.empty IntMap.empty IntMap.empty IntMap.empty Map.empty IntMap.empty (_ProgramTypeEnv env)

closedType :: MonoType Int -> Bool
closedType typ = case typ of
    TyCon _ -> True
    TyApp left right -> closedType left && closedType right
    _ -> False

lookupToken :: MonadIO m => String -> IORef (Map.Map Word64 a) -> Word64 -> ExceptT KernelErr m a
lookupToken name table token = do
    values <- liftIO (readIORef table)
    maybe (throwE (BackendError ("unknown native " ++ name ++ " token"))) return (Map.lookup token values)

freshToken :: MonadIO m => Session -> ExceptT KernelErr m Word64
freshToken session = do
    next <- liftIO (readIORef (sessionNextToken session))
    when (next >= fromIntegral (maxBound :: Int64)) (throwE (BackendError "native host-state identifier overflow"))
    liftIO (writeIORef (sessionNextToken session) (next + 1))
    return next

installReply :: UniqueM m => Session -> Native.NativeRequest -> Context -> Services.ServiceResult -> ExceptT KernelErr m ()
installReply session request before reply = case reply of
    Services.ServiceReject -> send 0 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceFailure -> send 0 (Native.requestHostState request) (Native.requestPremises request) []
    Services.ServiceContinue next premises -> accept (if equality then 2 else 1) next premises []
    Services.ServiceUndecided next premises -> accept 4 next premises []
    Services.ServiceUnify next premises left right -> accept 1 next premises [(left, right)]
    Services.ServiceEquality decision next premises -> accept (case decision of Just True -> 2; Just False -> 3; Nothing -> 4) next premises []
    where
        equality = Native.requestKind request == 5
        send status state premises pairs = do
            words <- encodeTermPairs session pairs
            liftIO (Native.resume (sessionMachine session) status state premises words) >>= nativeResult
        accept status next premises pairs = do
            let constraints = [constraint | constraint <- _LeftConstraints next, not (disagreement constraint)]
                changed = [(mkLVar variable, value) | (variable, value) <- Map.toList (unVarBinding (_TotalVarBinding next)), Map.lookup variable (unVarBinding (_TotalVarBinding before)) /= Just value]
            state <- if null constraints then return 0 else do
                token <- freshToken session
                liftIO (modifyIORef' (sessionConstraints session) (Map.insert token constraints))
                return token
            premise <- if Native.requestKind request /= 3 then return (Native.requestPremises request) else if nullArithStore premises then return 0 else do
                token <- freshToken session
                liftIO (modifyIORef' (sessionPremises session) (Map.insert token premises))
                return token
            send status state premise (changed ++ pairs)
        disagreement DisagreementConstraint {} = True
        disagreement _ = False

currentContext :: MonadIO m => Session -> Word64 -> Word64 -> VarBinding -> [Disagreement] -> ExceptT KernelErr m Context
currentContext session token callId binding disagreements = do
    constraints <- lookupToken "constraint" (sessionConstraints session) token
    bridge <- liftIO (readIORef (sessionBridge session))
    when (toInteger callId > toInteger (maxBound :: Int)) (throwE (BackendError "native call identifier overflow"))
    let labeling = refineBindingTypes (sessionEnvironment session) binding (bridgeLabeling bridge)
    return (Context binding labeling (map DisagreementConstraint disagreements ++ constraints) (Unique (fromIntegral callId)) (sessionDebugging session))

debugInteraction :: MonadIO m => Session -> Context -> [Cell] -> ExceptT KernelErr m Bool
debugInteraction session ctx cells = do
    let env = sessionEnvironment session
        active = [(ctx, cells)]
        free = Set.fromList (fullVariables (sessionProgram session))
    liftIO $ do
        writeIORef (_StackRef env) active
        modifyIORef' (_NameCacheRef env) (recordVisibleLVarHints active)
        verbose <- readIORef (_VerboseTyping env)
        _PutStr env env ctx (showsCurrentState (_NotationDB env) verbose free (_TypeInfo env) ctx cells [] "") `onException` closeSession session
    updated <- liftIO (readIORef (_StackRef env))
    assertStack updated `seq` return (not (null updated))

type Decode m = StateT [Int64] (ExceptT KernelErr m)

data Decoded
    = Term TermNode
    | Formula P.MyPresburgerFormulaRep [P.MyVar] [TermNode] (Maybe SLoc)
    deriving ()

word :: Monad m => Decode m Int64
word = do
    words <- get
    case words of
        [] -> lift (throwE (BackendError "truncated native term buffer"))
        value : rest -> put rest >> return value

naturalWord :: Monad m => Decode m Int64
naturalWord = do
    value <- word
    when (value < 0) (lift (throwE (BackendError "negative native term field")))
    return value

countWord :: Monad m => Decode m Int
countWord = do
    value <- naturalWord
    when (toInteger value > toInteger (maxBound :: Int)) (lift (throwE (BackendError "native count exceeds host range")))
    return (fromIntegral value)

runDecode :: Monad m => Decode m a -> [Int64] -> ExceptT KernelErr m a
runDecode parser words = do
    (result, remaining) <- runStateT parser words
    unless (null remaining) (throwE (BackendError "trailing native term buffer words"))
    return result

metadata :: Session -> Int64 -> NodeMetadata
metadata session index = IntMap.findWithDefault (NodeMetadata Nothing noLamType Nothing) (fromIntegral index) (fullMetadata (sessionProgram session))

decodeTerm :: UniqueM m => Session -> Decode m TermNode
decodeTerm session = decoded >>= finish where
    finish (Term term) = return term
    finish Formula {} = lift (throwE (BackendError "incomplete native Presburger application"))
    decoded = do
        tag <- word
        case tag of
            0 -> do
                uid <- naturalWord
                scope <- countWord
                isType <- naturalWord
                meta <- word
                when (isType > 1) (lift (throwE (BackendError "invalid native variable kind")))
                variable <- lift (decodeVariable session (fromIntegral uid) scope (isType == 1) meta)
                return (Term (mkLVar variable))
            1 -> do
                symbol <- countWord
                meta <- word
                table <- liftIO (bridgeSymbols <$> readIORef (sessionBridge session))
                case IntMap.lookup symbol table of
                    Just (ConstantSymbol constant) -> return (Term (mkNConLoc (nodeLocation (metadata session meta)) constant))
                    Just (PresburgerSymbol rep [] loc) -> return (Term (NPresburgerCheck rep Map.empty loc))
                    Just (PresburgerSymbol rep vars loc) -> return (Formula rep vars [] loc)
                    Nothing -> lift (throwE (BackendError "unknown native constant symbol"))
            2 -> do
                meta <- word
                function <- decoded
                argument <- decodeTerm session
                case function of
                    Term term -> return (Term (mkNAppLoc (nodeLocation (metadata session meta)) term argument))
                    Formula rep names arguments loc ->
                        if length arguments + 1 == length names then
                            return (Term (NPresburgerCheck rep (Map.fromList (zip names (arguments ++ [argument]))) loc))
                        else
                            return (Formula rep names (arguments ++ [argument]) loc)
            3 -> Term . mkNIdx <$> countWord
            4 -> do
                meta <- word
                body <- decodeTerm session
                let info = metadata session meta
                return (Term (NLam (nodeHint info) (nodeType info) body (nodeLocation info)))
            5 -> do
                uid <- naturalWord
                scope <- countWord
                meta <- word
                constant <- lift (decodeNominal session (fromIntegral uid) scope meta)
                return (Term (mkNConLoc (nodeLocation (metadata session meta)) constant))
            6 -> do
                count <- countWord
                digits <- replicateM count word
                when (null digits || any (\digit -> digit < 48 || digit > 57) digits) (lift (throwE (BackendError "invalid native natural literal")))
                return (Term (mkNCon (DC_NatL (foldl (\value digit -> value * 10 + toInteger (digit - 48)) 0 digits))))
            7 -> return (Term (mkNCon DC_wc))
            _ -> lift (throwE (BackendError "invalid native term tag"))

decodeVariable :: UniqueM m => Session -> Word64 -> Int -> Bool -> Int64 -> ExceptT KernelErr m LogicVar
decodeVariable session uid scope isType meta = do
    bridge <- liftIO (readIORef (sessionBridge session))
    variable <- case Map.lookup uid (bridgeVariables bridge) of
        Just known -> return known
        Nothing -> do
            unique <- identityFor session uid
            return (if isType then LV_ty_var unique else LV_Unique unique (mkHint (nodeHint (metadata session meta))))
    bridge <- liftIO (readIORef (sessionBridge session))
    let encoded = [0, fromIntegral uid, fromIntegral scope, if isType then 1 else 0, meta]
        binders = case (variable, unLamType (nodeType (metadata session meta))) of
            (LV_ty_var unique, Just (TyMTV original)) -> Map.insert original unique (bridgeTypeBinders bridge)
            _ -> bridgeTypeBinders bridge
        label
            | isType && uid < bridgeQuerySlots bridge = bridgeLabeling bridge
            | otherwise = enrollLabel variable scope (bridgeLabeling bridge)
        withType = case (variable, fmap (instantiateMetadataType binders) (unLamType (nodeType (metadata session meta)))) of
            (LV_Named _, _) -> label
            (_, Just typ) -> label { _VarTypes = IntMap.insert (lvKey variable) typ (_VarTypes label) }
            _ -> label
        typed = if isType then withType { _TyVarKeys = IntMap.insert (lvKey variable) () (_TyVarKeys withType) } else withType
        uncertain = case variable of
            LV_Named _ -> isType
            _ -> isType || maybe True (not . closedType) (unLamType (nodeType (metadata session meta)))
    liftIO (writeIORef (sessionBridge session) bridge { bridgeVariables = Map.insert uid variable (bridgeVariables bridge), bridgeVariableWires = Map.insert variable encoded (bridgeVariableWires bridge), bridgeLabeling = typed, bridgeTypeBinders = binders, bridgeUncertain = bridgeUncertain bridge || uncertain })
    return variable

decodeNominal :: UniqueM m => Session -> Word64 -> Int -> Int64 -> ExceptT KernelErr m Constant
decodeNominal session uid scope meta = do
    bridge <- liftIO (readIORef (sessionBridge session))
    constant <- case Map.lookup uid (bridgeConstants bridge) of
        Just known -> return known
        Nothing -> do
            unique <- identityFor session uid
            return (DC (DC_Unique unique (mkHint (nodeHint (metadata session meta)))))
    bridge <- liftIO (readIORef (sessionBridge session))
    let encoded = [5, fromIntegral uid, fromIntegral scope, meta]
        labeling = enrollLabel constant scope (bridgeLabeling bridge)
        typed = case (constant, fmap (instantiateMetadataType (bridgeTypeBinders bridge)) (unLamType (nodeType (metadata session meta)))) of
            (DC (DC_Unique unique _), Just typ) -> labeling { _ConTypes = IntMap.insert (unUnique unique) typ (_ConTypes labeling) }
            _ -> labeling
        uncertain = maybe False (not . closedType) (unLamType (nodeType (metadata session meta)))
    liftIO (writeIORef (sessionBridge session) bridge { bridgeConstants = Map.insert uid constant (bridgeConstants bridge), bridgeConstantWires = Map.insert constant encoded (bridgeConstantWires bridge), bridgeLabeling = typed, bridgeUncertain = bridgeUncertain bridge || uncertain })
    return constant

decodeState :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m (VarBinding, [Disagreement])
decodeState session words = do
    resetLabeling session
    runDecode parser words
    where
        parser = do
            count <- countWord
            pairs <- replicateM count $ do
                variable <- decodeTerm session
                value <- decodeTerm session
                case variable of
                    LVar name -> return (name, value)
                    _ -> lift (throwE (BackendError "native state does not begin with a variable"))
            remaining <- countWord
            disagreements <- replicateM remaining ((:=?=:) <$> decodeTerm session <*> decodeTerm session)
            return (VarBinding (Map.fromList [(variable, value) | (variable, value) <- pairs, value /= mkLVar variable]), disagreements)

decodeRoots :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m [TermNode]
decodeRoots session = runDecode (countWord >>= \count -> replicateM count (decodeTerm session))

decodeFrames :: UniqueM m => Session -> [Int64] -> ExceptT KernelErr m [Cell]
decodeFrames session = runDecode $ do
    count <- countWord
    replicateM count $ do
        scope <- countWord
        callId <- countWord
        hypotheses <- countWord >>= \count -> replicateM count (decodeTerm session)
        goal <- decodeTerm session
        return (mkCell Map.empty hypotheses emptyArithStore scope goal (Unique callId))

encodePairs :: UniqueM m => Session -> [(LogicVar, TermNode)] -> ExceptT KernelErr m [Int64]
encodePairs session = encodeTermPairs session . map (\(variable, value) -> (mkLVar variable, value))

encodeTermPairs :: UniqueM m => Session -> [(TermNode, TermNode)] -> ExceptT KernelErr m [Int64]
encodeTermPairs session pairs = do
    encoded <- mapM (\(left, right) -> (++) <$> encodeTerm session left <*> encodeTerm session right) pairs
    return (fromIntegral (length pairs) : concat encoded)

encodeTerm :: UniqueM m => Session -> TermNode -> ExceptT KernelErr m [Int64]
encodeTerm session input = go (rewrite NF input) where
    go (LVar variable) = do
        bridge <- liftIO (readIORef (sessionBridge session))
        case Map.lookup variable (bridgeVariableWires bridge) of
            Just encoded -> return encoded
            Nothing -> do
                uid <- liftIO (Native.reserveUid (sessionMachine session)) >>= nativeResult
                let isType = case variable of LV_ty_var _ -> 1; _ -> 0
                    scope = lookupLabel variable (bridgeLabeling bridge)
                    encoded = [0, fromIntegral uid, fromIntegral scope, isType, -1]
                liftIO (writeIORef (sessionBridge session) bridge { bridgeVariables = Map.insert uid variable (bridgeVariables bridge), bridgeVariableWires = Map.insert variable encoded (bridgeVariableWires bridge) })
                return encoded
    go (NCon (DC (DC_NatL value)) _)
        | value >= 0 = return (6 : fromIntegral (length digits) : map (fromIntegral . ord) digits)
        | otherwise = throwE (BackendError "negative natural in a native binding")
        where
            digits = show value
    go (NCon (DC DC_wc) _) = return [7]
    go (NCon constant _) = do
        bridge <- liftIO (readIORef (sessionBridge session))
        case Map.lookup constant (bridgeConstantWires bridge) of
            Just nominal -> return nominal
            Nothing -> do
                symbol <- internSymbol session (ConstantSymbol constant)
                return [1, fromIntegral symbol, -1]
    go (NIdx index)
        | index >= 0 = return [3, fromIntegral index]
        | otherwise = throwE (BackendError "negative de Bruijn index in a native binding")
    go (NApp function argument _) = do
        lhs <- go function
        rhs <- go argument
        return ([2, -1] ++ lhs ++ rhs)
    go (NLam _ _ body _) = ([4, -1] ++) <$> go body
    go (NPresburgerCheck rep freeOf loc) = do
        symbol <- internSymbol session (PresburgerSymbol rep (Map.keys freeOf) loc)
        foldM (\function argument -> do value <- go argument; return ([2, -1] ++ function ++ value)) [1, fromIntegral symbol, -1] (Map.elems freeOf)
    go suspended@Susp {} = go (rewrite NF suspended)

internSymbol :: MonadIO m => Session -> FullSymbol -> ExceptT KernelErr m Int
internSymbol session symbol = do
    bridge <- liftIO (readIORef (sessionBridge session))
    case Map.lookup key (bridgeSymbolIndices bridge) of
        Just index -> return index
        Nothing -> do
            let index = IntMap.size (bridgeSymbols bridge)
            liftIO (Native.ensureSymbol (sessionMachine session) index (symbolRole symbol)) >>= nativeResult
            liftIO (writeIORef (sessionBridge session) bridge { bridgeSymbols = IntMap.insert index symbol (bridgeSymbols bridge), bridgeSymbolIndices = Map.insert key index (bridgeSymbolIndices bridge) })
            return index
    where
        key = symbolIdentity symbol

instantiateMetadataType :: Map.Map MetaTVar MetaTVar -> MonoType Int -> MonoType Int
instantiateMetadataType binders typ = case typ of
    TyMTV original -> TyMTV (Map.findWithDefault original original binders)
    TyApp left right -> TyApp (instantiateMetadataType binders left) (instantiateMetadataType binders right)
    _ -> typ

-- Unification-generated variables have no source annotation. Recover their
-- types from the typed variables whose values contain them, without copying
-- display hints or guessing a type for a missing application argument.
refineBindingTypes :: RuntimeEnv -> VarBinding -> Labeling -> Labeling
refineBindingTypes env (VarBinding binding) = improve where
    improve labeling
        | _VarTypes next == _VarTypes labeling = next
        | otherwise = improve next
        where
            inferred = concat
                [ collect labeling [] typ value
                | (variable, value) <- Map.toList binding
                , Just typ <- [lookupLVarType variable labeling]
                ]
            next = labeling { _VarTypes = foldl insert (_VarTypes labeling) inferred }
            insert types (LV_Named _, _) = types
            insert types (variable, typ) = IntMap.insertWith (\_ old -> old) (lvKey variable) typ types
    collect labeling bound expected value = case value of
        LVar variable -> [(variable, expected)]
        NLam _ _ body _ -> case splitArrowsHOPU 1 expected of
            Just ([domain], result) -> collect labeling (domain : bound) result body
            _ -> []
        _ -> case unfoldlNApp value of
            (LVar variable, arguments) -> case mapM (typeOfTerm labeling bound) arguments of
                Just domains -> [(variable, foldr mkTyArrow expected domains)]
                Nothing -> []
            (NCon (DC constructor) _, arguments) -> case Map.lookup constructor (_ProgramTypeEnv env) of
                Just (Forall parameters body) ->
                    let (typeArguments, values) = splitAt (length parameters) arguments
                    in case mapM (primitiveTypeArgumentWithKinds (_ProgramKindEnv env)) typeArguments of
                        Just replacements
                            | length replacements == length parameters -> case substitute replacements body >>= splitArrowsHOPU (length values) of
                                Just (domains, _) -> concat (zipWith (collect labeling bound) domains values)
                                Nothing -> []
                        _ -> []
                Nothing -> []
            _ -> []
    substitute replacements typ = case typ of
        TyVar index
            | index >= 0 && index < length replacements -> Just (replacements !! index)
            | otherwise -> Nothing
        TyApp left right -> TyApp <$> substitute replacements left <*> substitute replacements right
        _ -> Just typ

applyPending :: UniqueM m => Session -> ExceptT KernelErr m ()
applyPending session = do
    let pendingRef = _PendingSubst (sessionEnvironment session)
    pending <- liftIO (readIORef pendingRef)
    unless (Map.null (unVarBinding pending)) $ do
        words <- encodePairs session (Map.toList (unVarBinding pending))
        liftIO (Native.assign (sessionMachine session) words) >>= nativeResult
        liftIO (writeIORef pendingRef mempty)

-- Arithmetic quantifier order follows creation order, including unseen UID gaps.
identityFor :: UniqueM m => Session -> Word64 -> ExceptT KernelErr m Unique
identityFor session uid = do
    bridge <- liftIO (readIORef (sessionBridge session))
    case Map.lookup uid (bridgeIdentities bridge) of
        Just unique -> return unique
        Nothing
            | uid < bridgeQuerySlots bridge -> throwE (BackendError "native identity collides with a query slot")
            | uid < bridgeNextIdentity bridge -> case Map.lookupLE uid (bridgeIdentityBlocks bridge) of
                Just (start, block) -> uniqueAt (uid - start) block >>= remember
                Nothing -> throwE (BackendError "missing native identity reservation")
            | otherwise -> do
                let start = bridgeNextIdentity bridge
                    count = toInteger uid - toInteger start + 1
                when (count > toInteger (maxBound :: Int)) (throwE (BackendError "native identity reservation exceeds host range"))
                reserved <- getUniqueBlock (fromInteger count)
                block <- maybe (throwE (BackendError "native identity reservation exhausted")) return reserved
                unique <- uniqueAt (uid - start) block
                liftIO (modifyIORef' (sessionBridge session) (\current -> current { bridgeIdentityBlocks = if count > 1 then Map.insert start block (bridgeIdentityBlocks current) else bridgeIdentityBlocks current, bridgeNextIdentity = uid + 1 }))
                remember unique
    where
        uniqueAt offset block
            | toInteger offset > toInteger (maxBound :: Int) = throwE (BackendError "native identity offset exceeds host range")
            | otherwise = maybe (throwE (BackendError "invalid native identity reservation")) return (lookupUniqueBlock (fromIntegral offset) block)
        remember unique = do
            liftIO (modifyIORef' (sessionBridge session) (\bridge -> bridge { bridgeIdentities = Map.insert uid unique (bridgeIdentities bridge) }))
            return unique
