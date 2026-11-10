module Main where

import qualified Calc.Presburger.Internal as P
import Control.Exception (IOException, try)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU
import qualified Hol.BETA.Main as BETA
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Hol.V1.FullBytecode
import Hol.V1.FullCompiler
import qualified Hol.V1.FullRuntime as Full
import System.Timeout (timeout)
import qualified X.HigherMachine as Native
import Z.Utils

check :: String -> Bool -> IO ()
check name okay = unless okay (ioError (userError name))

right :: Either String a -> IO a
right = either (ioError . userError) return

kernel :: Either KernelErr a -> IO a
kernel = either (const (ioError (userError "unexpected V1 runtime error"))) return

makeEnvironment :: IO (RuntimeEnv, IORef [TermNode], IORef [TermNode], IORef Int)
makeEnvironment = do
    pending <- newIORef mempty
    debugging <- newIORef False
    verbose <- newIORef False
    stack <- newIORef []
    names <- newIORef initialCache
    output <- newIORef []
    input <- newIORef [mkNCon (DC_NatL 8), mkNCon (DC_NatL 9)]
    reads <- newIORef 0
    let env = RuntimeEnv
            { _PutStr = \_ _ _ -> return ()
            , _Answer = \_ -> return True
            , _PrintPrimitive = \_ term -> modifyIORef' output (++ [term])
            , _ReadPrimitive = \_ _ -> do
                modifyIORef' reads (+ 1)
                remaining <- readIORef input
                case remaining of
                    [] -> return Nothing
                    value : rest -> writeIORef input rest >> return (Just value)
            , _TypeInfo = Map.empty
            , _PendingSubst = pending
            , _ProgramKindEnv = BETA.theInitialKindDecls
            , _ProgramTypeEnv = BETA.theInitialTypeDecls
            , _VerboseTyping = verbose
            , _StackRef = stack
            , _NameCacheRef = names
            , _DebuggingRef = debugging
            , _NotationDB = Notation.initial
            , _ModuleName = "full-runtime-regression"
            , _QueryCallId = Nothing
            }
    return (env, output, input, reads)

program :: RuntimeEnv -> [TermNode] -> TermNode -> IO FullProgram
program env facts query = withRuntimeMetadata (_ProgramKindEnv env) (_ProgramTypeEnv env) (_TypeInfo env) <$> right (compileFullProgram facts query)

withSession :: RuntimeEnv -> FullProgram -> (Full.Session -> IO a) -> IO a
withSession env = Full.withSession env (_DebuggingRef env)

next :: Full.Session -> UniqueT IO (Maybe Context)
next session = runExceptT (Full.nextSolution session) >>= liftIO . kernel

main :: IO ()
main = do
    (base, output, _, reads) <- makeEnvironment
    let x = LV_Named "X"
        variable = mkLVar x
        name = mkNCon . DC_Named
        nat = mkNCon . DC_NatL
        call arg = mkNApp (name "p") arg
        conjunction left right = foldlNApp (mkNCon LO_and) [left, right]
        disjunction left right = foldlNApp (mkNCon LO_or) [left, right]
        clause head body = foldlNApp (mkNCon LO_if) [head, body]
        value answer = fmap (\ctx -> bindVars (_TotalVarBinding ctx) variable) answer
        done = maybe True (const False)
    cutCode <- program base [clause (call (name "red")) (mkNCon LO_cut), call (name "blue")] (call variable)
    withSession base cutCode $ \session -> execUniqueT $ do
        high <- runExceptT (Full.identityFor session 100000) >>= liftIO . kernel
        low <- runExceptT (Full.identityFor session 42) >>= liftIO . kernel
        repeated <- runExceptT (Full.identityFor session 100000) >>= liftIO . kernel
        bridge <- liftIO (readIORef (Full.sessionBridge session))
        liftIO (check "native identity blocks preserve creation order without storing skipped IDs" (Map.size (Full.bridgeIdentities bridge) == 2 && Map.size (Full.bridgeIdentityBlocks bridge) == 1 && low < high && high == repeated))
        collision <- runExceptT (Full.identityFor session 0)
        liftIO (check "query identity collision boundary does not move with sparse IDs" (either (const True) (const False) collision))
        firstSymbol <- runExceptT (Full.internSymbol session (ConstantSymbol (DC (DC_Unique (Unique 999) (mkHint (Just "first")))))) >>= liftIO . kernel
        renamedSymbol <- runExceptT (Full.internSymbol session (ConstantSymbol (DC (DC_Unique (Unique 999) (mkHint (Just "renamed")))))) >>= liftIO . kernel
        liftIO (check "runtime symbol indexing preserves identity despite display hints" (firstSymbol == renamedSymbol))
    withSession base cutCode $ \session -> execUniqueT $ do
        saved <- liftIO (Full.takeSnapshot session >>= right)
        first <- next session
        exhausted <- next session
        liftIO (check "native cut commits its remaining clauses" (value first == Just (name "red") && done exhausted))
        liftIO (Full.restoreSnapshot session saved >>= right)
        liftIO (writeIORef (_PendingSubst base) (VarBinding (Map.singleton x (name "blue"))))
        restored <- next session
        liftIO (check "restoring before cut recovers pruned alternatives" (value restored == Just (name "blue")))
        liftIO $ withSession base cutCode $ \other -> do
            otherOwner <- Full.restoreSnapshot other saved
            check "snapshot owner prevents crossing sessions" (either (const True) (const False) otherOwner)
        liftIO (Full.closeSnapshot saved)
        closed <- liftIO (Full.restoreSnapshot session saved)
        liftIO (check "closed snapshot cannot be restored" (either (const True) (const False) closed))

    writeIORef (_PendingSubst base) (VarBinding (Map.singleton x (name "blue")))
    choiceCode <- program base [call (name "red"), call (name "blue"), call (name "green")] (call variable)
    withSession base choiceCode $ \session -> execUniqueT $ do
        selected <- next session
        exhausted <- next session
        liftIO (check "initial pending assignment restricts every alternative" (value selected == Just (name "blue") && done exhausted))

    answers <- newIORef []
    callbacks <- newIORef (0 :: Int)
    let callbackEnv = base
            { _Answer = \ctx -> do
                modifyIORef' answers (++ [bindVars (_TotalVarBinding ctx) variable])
                count <- readIORef callbacks
                when (count == 0) (writeIORef (_PendingSubst base) (VarBinding (Map.singleton x (name "blue"))))
                modifyIORef' callbacks (+ 1)
                return True
            }
    callbackCode <- program callbackEnv [call (name "red"), call (name "blue")] (disjunction (mkNCon LO_true) (call variable))
    _ <- execUniqueT (runExceptT (Full.runFullProgram callbackEnv (_DebuggingRef callbackEnv) callbackCode)) >>= kernel
    observed <- readIORef answers
    check "answer callback assignment applies to future choices" (observed == [variable, name "blue"])

    let natEnv = base { _TypeInfo = Map.singleton x mkTyNat }
        ioQuery = conjunction (mkNApp (name "print") (nat 7)) (mkNApp (name "read") variable)
    ioCode <- program natEnv [] ioQuery
    withSession natEnv ioCode $ \session -> execUniqueT $ do
        saved <- liftIO (Full.takeSnapshot session >>= right)
        first <- next session
        liftIO (Full.restoreSnapshot session saved >>= right)
        second <- next session
        liftIO (check "snapshot replay consumes fresh primitive input" (value first == Just (nat 8) && value second == Just (nat 9)))
        liftIO (Full.closeSnapshot saved)
    printed <- readIORef output
    consumed <- readIORef reads
    check "snapshot does not undo print or read effects" (printed == [nat 7, nat 7] && consumed == 2)

    let comparison = foldlNApp (mkNCon DC_gt) [variable, nat 1]
        constrained = conjunction comparison (disjunction (mkNCon LO_true) (mkNCon LO_true))
    constrainedCode <- program natEnv [] constrained
    withSession natEnv constrainedCode $ \session -> execUniqueT $ do
        first <- next session
        liftIO (check "unknown arithmetic constraint remains at an answer" (maybe False (not . null . _LeftConstraints) first))
        saved <- liftIO (Full.takeSnapshot session >>= right)
        liftIO (writeIORef (_PendingSubst natEnv) (VarBinding (Map.singleton x (nat 0))))
        rejected <- next session
        liftIO (check "pending assignment rechecks the restored host constraint state" (done rejected))
        liftIO (Full.restoreSnapshot session saved >>= right)
        restored <- next session
        liftIO (check "snapshot restores native choices and host residual tokens" (maybe False (not . null . _LeftConstraints) restored && value restored == Just variable))
        liftIO (Full.closeSnapshot saved)
    let equality = NPresburgerCheck (P.EqnF (P.IVar 1) (P.IVar 2)) (Map.fromList [(1, mkNIdx 0), (2, mkNIdx 1)]) Nothing
        binder operator hint body = mkNApp (mkNCon operator) (mkNLamHintTy (Just hint) (LamType (Just mkTyNat)) body)
        forallExists = binder LO_pi "C" (binder LO_sigma "X" equality)
        existsForall = binder LO_sigma "X" (binder LO_pi "C" equality)
        pendingCall = mkNApp (name "q") (mkNIdx 0)
        metadataQuery = binder LO_pi "C" (conjunction (mkNApp (name "print") (nat 0)) (conjunction pendingCall pendingCall))
    metadataCode <- program base [] metadataQuery
    let inspectMetadata compact = withSession base metadataCode $ \session -> execUniqueT $ do
            step <- liftIO ((if compact then Native.nextStepForHost else Native.nextStep) (Full.sessionMachine session) >>= right)
            case step of
                Native.Request request -> do
                    _ <- runExceptT (Full.decodeState session (Native.requestState request)) >>= liftIO . kernel
                    _ <- runExceptT (Full.decodeRoots session (Native.requestTerms request)) >>= liftIO . kernel
                    _ <- runExceptT (Full.decodeFrames session (Native.requestFrames request)) >>= liftIO . kernel
                    _ <- runExceptT (Full.decodeRoots session (Native.requestDeclarations request)) >>= liftIO . kernel
                    bridge <- liftIO (readIORef (Full.sessionBridge session))
                    let labeling = Full.bridgeLabeling bridge
                    liftIO (check "compact requests retain frame-only nominal declarations" (not (Map.null (Full.bridgeConstants bridge))))
                    liftIO (check "nondebug compact request avoids exporting full frames" (not compact || Native.requestFrames request == [0]))
                    return (Full.bridgeVariables bridge, Full.bridgeConstants bridge, Full.bridgeIdentities bridge, _ConLabel labeling, _ConTypes labeling, _VarLabel labeling, _VarTypes labeling, _TyVarKeys labeling)
                _ -> liftIO (ioError (userError "metadata fixture produced no primitive event"))
    legacyMetadata <- inspectMetadata False
    compactMetadata <- inspectMetadata True
    check "compact frame metadata preserves identities, kinds, types and scopes" (legacyMetadata == compactMetadata)
    metadataTemplate <- program base [] (mkNCon LO_true)
    let originalType = Unique 900000
        repeatedCode = metadataTemplate
            { fullWords = take 7 (fullWords metadataTemplate) ++ [2] ++ drop 8 (fullWords metadataTemplate)
            , fullMetadata = IntMap.fromList
                [ (0, NodeMetadata (Just "T") (LamType (Just (TyMTV originalType))) Nothing)
                , (1, NodeMetadata (Just "C") (LamType (Just (TyMTV originalType))) Nothing)
                ]
            }
        firstType = [0, 10, 0, 1, 0]
        laterType = [0, 11, 0, 1, 0]
        nominal = [5, 12, 1, 1]
        fullFrames = [2, 1, 0, 0, 2, -1] ++ firstType ++ nominal
            ++ [1, 1, 0, 2, -1] ++ laterType ++ nominal
        declarations = [4] ++ firstType ++ nominal ++ laterType ++ nominal
        deduplicated = [3] ++ firstType ++ nominal ++ laterType
        inspectRepeated frames words = withSession base repeatedCode $ \session -> execUniqueT $ do
            if frames then void (runExceptT (Full.decodeFrames session words) >>= liftIO . kernel)
            else void (runExceptT (Full.decodeRoots session words) >>= liftIO . kernel)
            bridge <- liftIO (readIORef (Full.sessionBridge session))
            return (Full.bridgeTypeBinders bridge, _ConTypes (Full.bridgeLabeling bridge))
    repeatedFrames <- inspectRepeated True fullFrames
    repeatedDeclarations <- inspectRepeated False declarations
    uniqueDeclarations <- inspectRepeated False deduplicated
    check "repeated declarations re-enroll nominal types after source type-binder changes"
        (repeatedFrames == repeatedDeclarations && repeatedDeclarations /= uniqueDeclarations
            && repeatedDeclarations == (Map.singleton originalType (Unique 11), IntMap.singleton 12 (TyMTV (Unique 11))))
    ordered <- program base [] forallExists
    reversed <- program base [] existsForall
    withSession base ordered $ \session -> execUniqueT $ do
        answer <- next session
        liftIO (check "native identity decoding preserves forall-before-exists" (not (done answer)))
    withSession base reversed $ \session -> execUniqueT $ do
        answer <- next session
        liftIO (check "native identity decoding preserves exists-before-forall" (done answer))

    withSession base choiceCode $ \session -> execUniqueT $ do
        saved <- liftIO (Full.takeSnapshot session >>= right)
        liftIO (Full.setWorkLimit session 1 >>= right)
        invalid <- liftIO (Full.setWorkLimit session 0)
        unchanged <- liftIO (Full.getWorkLimit session >>= right)
        liftIO (check "invalid zero work limit preserves the previous setting" (either (const True) (const False) invalid && unchanged == 1))
        limited <- runExceptT (Full.nextSolution session)
        liftIO (check "work exhaustion is an explicit runtime error, not logical failure" (case limited of Left (BackendError message) -> "work limit" `isInfixOf` message; _ -> False))
        liftIO (Full.setWorkLimit session 100000 >>= right)
        liftIO (Full.restoreSnapshot session saved >>= right)
        enlarged <- liftIO (Full.getWorkLimit session >>= right)
        resumed <- next session
        liftIO (check "snapshot restoration preserves an enlarged work limit and resumes proof search" (enlarged == 100000 && value resumed == Just (name "red")))
        liftIO (Full.closeSnapshot saved)

    debugCount <- newIORef (0 :: Int)
    quitDebugging <- newIORef True
    let quitEnv = base
            { _DebuggingRef = quitDebugging
            , _PutStr = \runtime _ _ -> do
                count <- readIORef debugCount
                modifyIORef' debugCount (+ 1)
                when (count == 1) (runRuntime cmdQuit runtime)
            }
        quitQuery = disjunction (call (name "red")) (call (name "blue"))
    quitCode <- program quitEnv [call (name "red"), call (name "blue")] quitQuery
    withSession quitEnv quitCode $ \session -> execUniqueT $ do
        saved <- liftIO (Full.takeSnapshot session >>= right)
        quit <- next session
        again <- next session
        liftIO (check "debugger quit remains exhausted across repeated nextSolution calls" (done quit && done again))
        liftIO (Full.restoreSnapshot session saved >>= right)
        liftIO (writeIORef quitDebugging False)
        resumed <- next session
        liftIO (check "explicit snapshot restoration can resume a quit session" (not (done resumed)))
        liftIO (Full.closeSnapshot saved)

    let loop = name "loop"
    loopingCode <- program base [clause loop loop] loop
    withSession base loopingCode $ \session -> do
        stopped <- timeout 100000 (execUniqueT (next session))
        check "optimized native loops must remain interruptible" (done stopped)
        closed <- Full.getWorkLimit session
        check "cancellation closes the native session immediately" (either (const True) (const False) closed)

    let throwing = natEnv
            { _PrintPrimitive = \_ _ -> ioError (userError "print callback failed")
            , _ReadPrimitive = \_ _ -> ioError (userError "read callback failed")
            }
    forM_ [mkNApp (name "print") (nat 1), mkNApp (name "read") variable] $ \goal -> do
        code <- program throwing [] goal
        withSession throwing code $ \session -> do
            outcome <- try (execUniqueT (runExceptT (Full.nextSolution session))) :: IO (Either IOException (Either KernelErr (Maybe Context)))
            closed <- Full.getWorkLimit session
            check "primitive callback exceptions close the native session immediately" (either (const True) (const False) outcome && either (const True) (const False) closed)
    putStrLn "V1 full runtime: snapshots, assignment, host state, I/O, work limits and exception cleanup passed"
