module LoL.Hol.Session where

import Control.Concurrent.MVar
import Control.Exception (IOException, mask, onException, try)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (runReaderT)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Unique as Token
import Data.Word (Word64)
import Hol.BETA.Debugger (initialCache)
import Hol.BETA.Diagnostic (DiagnosticMode (..))
import Hol.BETA.Header (KindEnv, TypeEnv)
import Hol.BETA.HOPU
import qualified Hol.BETA.Main as BETA
import Hol.BETA.ModuleLoader
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Hol.V1.FullCompiler
import qualified Hol.V1.FullRuntime as Full
import LoL.Core (Term)
import LoL.Hol.Embed
import System.Timeout (timeout)
import Z.Utils

-- The clauses of the kernel are compiled once, when it is loaded. The cache
-- is an engine that holds them together with the facts of one environment.
data Kernel
    = Kernel
        { kernelKinds :: KindEnv
        , kernelTypes :: TypeEnv
        , kernelReady :: PreparedProgram
        , kernelFresh :: IORef Int
        , kernelCache :: MVar (Maybe Loaded)
        }
    deriving ()

-- The name of one environment that has declarations. No two environments share
-- a stamp, whichever kernel admitted their declarations.
newtype Stamp
    = Stamp Token.Unique
    deriving (Eq)

instance Show Stamp where
    show (Stamp unique) = "Stamp " ++ show (Token.hashUnique unique)

newStamp :: IO Stamp
newStamp = Stamp <$> Token.newUnique

-- The engine holds exactly the facts of the environment `loadedSource`; the
-- environment without declarations is Nothing.
data Loaded
    = Loaded
        { loadedEngine :: Full.Engine
        , loadedSource :: Maybe Stamp
        }
    deriving ()

data Limits
    = Limits
        { limitMicros :: Int
        , limitVisits :: Maybe Word64
        }
    deriving (Eq, Show)

-- The three results of a ground run (doc/LoLALPHA1.txt, 5.3, R3 to R5).
data Verdict
    = Admitted [Term]
    | Rejected (Maybe Report)
    | Undecided String
    deriving (Eq, Show)

defaultLimits :: Limits
defaultLimits = Limits { limitMicros = 60000000, limitVisits = Nothing }

loadKernel :: FilePath -> IO (Either String Kernel)
loadKernel path = do
    fresh <- newIORef 0
    loaded <- runReaderT (runUniqueT (loadMainWithDiagnostic DiagnosticTest BETA.theInitialKindDecls BETA.theInitialTypeDecls BETA.theInitialFactDecls path)) fresh
    cache <- newMVar Nothing
    return (fmap ($ cache) (loaded >>= fromModule fresh . loadedMain))
    where
        fromModule fresh env = do
            ready <- prepareFullProgram (moduleEnvKinds env) (moduleEnvTypes env) (moduleEnvFacts env)
            return (\cache -> Kernel { kernelKinds = moduleEnvKinds env, kernelTypes = moduleEnvTypes env, kernelReady = ready, kernelFresh = fresh, kernelCache = cache })

-- R1: the query has no logic variable other than its outputs. The run gets a
-- machine of its own, with the kernel and the given facts.
groundRun :: Kernel -> Limits -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
groundRun kernel limits facts goal outputs
    | Set.null (getLVars facts) && Set.isSubsetOf (getLVars goal) (Set.fromList outputs) = runGoal kernel limits facts goal outputs
    | otherwise = return (Undecided "the query has a logic variable that is not an output")

runGoal :: Kernel -> Limits -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
runGoal kernel limits facts goal outputs
    = case compilePreparedProgram (kernelReady kernel) Map.empty facts goal of
        Left message -> return (Undecided message)
        Right compiled -> do
            printed <- newIORef []
            env <- runtimeEnv kernel printed
            outcome <- timeout (limitMicros limits) (try (Full.withSession env (_DebuggingRef env) compiled (firstAnswer kernel limits)))
            reports <- readIORef printed
            return (verdictOf outputs reports outcome)

-- A ground run on the cached engine, which holds the kernel and the facts of
-- the environment `source`. `facts` are all the facts of that environment: they
-- are read only when the engine holds another environment and is built again.
-- An engine that cannot leave the run is dropped.
loadedRun :: Kernel -> Limits -> Maybe Stamp -> [TermNode] -> TermNode -> [LogicVar] -> IO Verdict
loadedRun kernel limits source facts goal outputs
    | not (Set.isSubsetOf (getLVars goal) (Set.fromList outputs)) = return (Undecided "the query has a logic variable that is not an output")
    | otherwise = withCache kernel $ \cached -> do
        synced <- sync cached
        case synced of
            Left message -> return (Nothing, Undecided message)
            Right loaded -> do
                printed <- newIORef []
                env <- runtimeEnv kernel printed
                outcome <- timeout (limitMicros limits) (try (Full.withQuery env (_DebuggingRef env) (loadedEngine loaded) Map.empty goal (firstAnswer kernel limits)))
                reports <- readIORef printed
                usable <- Full.leaveEngine (loadedEngine loaded)
                kept <- either (\_ -> Nothing <$ Full.closeEngine (loadedEngine loaded)) (\() -> return (Just loaded)) usable
                return (kept, verdictOf outputs reports (fmap (fmap (either Left id)) outcome))
    where
        sync cached = case cached of
            Just loaded
                | loadedSource loaded == source -> return (Right loaded)
            _ -> do
                mapM_ (Full.closeEngine . loadedEngine) cached
                created <- Full.createEngine (kernelReady kernel)
                case created of
                    Left message -> return (Left message)
                    Right engine -> do
                        extended <- extendAll engine facts
                        either (\message -> Left message <$ Full.closeEngine engine) (\() -> return (Right (Loaded engine source))) extended
        -- An environment is loaded in pieces, so that no fragment is large.
        extendAll engine remaining = case splitAt 512 remaining of
            ([], _) -> return (Right ())
            (piece, rest) -> Full.extendEngine engine piece >>= either (return . Left) (\() -> extendAll engine rest)

-- The environment `next` is `source` with the declaration that has `facts`:
-- an engine that holds `source` takes the facts and holds `next`.
loadedExtend :: Kernel -> Maybe Stamp -> Stamp -> [TermNode] -> IO ()
loadedExtend kernel source next facts = withCache kernel $ \cached -> case cached of
    Just loaded
        | loadedSource loaded == source -> do
            extended <- Full.extendEngine (loadedEngine loaded) facts
            kept <- either (\_ -> Nothing <$ Full.closeEngine (loadedEngine loaded)) (\() -> return (Just loaded { loadedSource = Just next })) extended
            return (kept, ())
    _ -> return (cached, ())

-- One caller at a time. An exception drops the engine.
withCache :: Kernel -> (Maybe Loaded -> IO (Maybe Loaded, a)) -> IO a
withCache kernel action = mask $ \restore -> do
    cached <- takeMVar (kernelCache kernel)
    (next, result) <- restore (action cached) `onException` (mapM_ (Full.closeEngine . loadedEngine) cached >> putMVar (kernelCache kernel) Nothing)
    putMVar (kernelCache kernel) next
    return result

-- R2: the first answer is the answer.
firstAnswer :: Kernel -> Limits -> Full.Session -> IO (Either String (Maybe Context))
firstAnswer kernel limits session = do
    limited <- maybe (return (Right ())) (Full.setWorkLimit session) (limitVisits limits)
    case limited of
        Left message -> return (Left message)
        Right () -> do
            answer <- runReaderT (runUniqueT (runExceptT (Full.nextSolution session))) (kernelFresh kernel)
            return (either (Left . describeError) Right answer)

verdictOf :: [LogicVar] -> [TermNode] -> Maybe (Either IOException (Either String (Maybe Context))) -> Verdict
verdictOf outputs reports outcome
    = case outcome of
        Nothing -> Undecided "the time limit was reached"
        Just (Left exception) -> Undecided (show exception)
        Just (Right (Left message)) -> Undecided message
        Just (Right (Right Nothing)) -> Rejected (listToMaybe (mapMaybe (either (const Nothing) Just . recoverReport) reports))
        Just (Right (Right (Just ctx)))
            | not (null (_LeftConstraints ctx)) -> Undecided "the answer has a residual constraint"
            | otherwise -> either Undecided Admitted (mapM (outputOf ctx) outputs)

-- R3: an output that still contains a logic variable does not admit.
outputOf :: Context -> LogicVar -> Either String Term
outputOf ctx output
    | Set.null (getLVars value) = recoverTerm value
    | otherwise = Left "the answer has a logic variable"
    where
        value = rewrite NF (bindVars (_TotalVarBinding ctx) (mkLVar output))

describeError :: KernelErr -> String
describeError err
    = case err of
        BackendError message -> message
        BadGoalGiven goal -> "bad goal: " ++ display goal
        BadFactGiven fact -> "bad fact: " ++ display fact
        UnsupportedArithmeticConstraint term -> "unsupported arithmetic constraint: " ++ display term

runtimeEnv :: Kernel -> IORef [TermNode] -> IO RuntimeEnv
runtimeEnv kernel printed = do
    pending <- newIORef (VarBinding Map.empty)
    debugging <- newIORef False
    verbose <- newIORef False
    stack <- newIORef []
    names <- newIORef initialCache
    return RuntimeEnv
        { _PutStr = \_ _ _ -> return ()
        , _Answer = \_ -> return True
        , _PrintPrimitive = \ctx term -> modifyIORef' printed (++ [rewrite NF (bindVars (_TotalVarBinding ctx) term)])
        , _ReadPrimitive = \_ _ -> return Nothing
        , _TypeInfo = Map.empty
        , _PendingSubst = pending
        , _ProgramKindEnv = kernelKinds kernel
        , _ProgramTypeEnv = kernelTypes kernel
        , _VerboseTyping = verbose
        , _StackRef = stack
        , _NameCacheRef = names
        , _DebuggingRef = debugging
        , _NotationDB = Notation.initial
        , _ModuleName = "lol"
        , _QueryCallId = Nothing
        }
