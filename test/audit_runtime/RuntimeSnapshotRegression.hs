module Main where

import Control.Monad (unless)
import Control.Monad.Trans.Except (runExceptT)
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU (Labeling (..), LogicVarSubst)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import System.Exit (exitFailure)
import Z.Utils (Unique (..), execUniqueT)

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("runtime snapshot regression failed: " ++ label)
    exitFailure

mkRuntimeEnv :: IORef Stack -> IORef LogicVarSubst -> IORef NameCache -> IORef [String] -> IORef Int -> IO RuntimeEnv
mkRuntimeEnv stackRef pendingRef cacheRef outputRef inputRef = do
    verboseRef <- newIORef False
    debuggingRef <- newIORef False
    return RuntimeEnv
        { _PutStr = \_ _ line -> modifyIORef' outputRef (++ [line])
        , _Answer = \_ -> return False
        , _PrintPrimitive = \_ term -> modifyIORef' outputRef (++ [show term])
        , _ReadPrimitive = \_ _ -> modifyIORef' inputRef (+ 1) >> return Nothing
        , _TypeInfo = Map.empty
        , _PendingSubst = pendingRef
        , _ProgramTypeEnv = Map.empty
        , _VerboseTyping = verboseRef
        , _StackRef = stackRef
        , _NameCacheRef = cacheRef
        , _DebuggingRef = debuggingRef
        , _NotationDB = Notation.initial
        , _ModuleName = "snapshot-regression"
        }

main :: IO ()
main = do
    contextDebugRef <- newIORef False
    let cutId = Unique 10
        emptyLabeling = Labeling
            { _ConLabel = IntMap.empty
            , _VarLabel = IntMap.empty
            , _ConTypes = IntMap.empty
            , _VarTypes = IntMap.empty
            , _NamedTypes = Map.empty
            , _TyVarKeys = IntMap.empty
            , _TypeEnv = Map.empty
            }
        context = Context
            { _TotalVarBinding = mempty
            , _CurrentLabeling = emptyLabeling
            , _LeftConstraints = []
            , _ContextThreadId = cutId
            , _debuggindModeOn = contextDebugRef
            }
        cell goal = mkCell Map.empty [] ([], []) 0 (mkNCon goal) cutId
        preCutStack =
            [ (context, [cell LO_cut, cell LO_fail])
            , (context, [cell LO_true])
            ]
    stackRef <- newIORef preCutStack
    pendingRef <- newIORef mempty
    let oldVar = LV_Named "Old"
        newVar = LV_Named "New"
    cacheRef <- newIORef (recordRename oldVar "Old" initialCache)
    outputRef <- newIORef []
    inputRef <- newIORef 0
    env <- mkRuntimeEnv stackRef pendingRef cacheRef outputRef inputRef

    saved <- runRuntime snapshot env
    cutResult <- execUniqueT (runExceptT (runTransition env Set.empty preCutStack))
    assert "executed cut did not prune the same-activation alternative"
        (case cutResult of Right False -> True; _ -> False)

    _PrintPrimitive env (error "unused print context") (mkNCon (DC_NatL 7))
    _ <- _ReadPrimitive env (error "unused read context") (error "unused read term")
    modifyIORef' cacheRef (recordRename newVar "New")
    restored <- runRuntime (restore saved) env
    assert "same-runtime restore failed" (either (const False) (const True) restored)
    restoredStack <- readIORef stackRef
    assert "pre-cut alternatives were not restored" (length restoredStack == length preCutStack)
    outputAfterRestore <- readIORef outputRef
    inputAfterRestore <- readIORef inputRef
    assert "restore rewound print effects" (length outputAfterRestore == 1)
    assert "restore rewound read effects" (inputAfterRestore == 1)
    cacheAfterRestore <- readIORef cacheRef
    assert "restore discarded a post-snapshot display name" (toDisplay newVar cacheAfterRestore == Just "New")
    assert "restore lost a pre-snapshot display name" (toDisplay oldVar cacheAfterRestore == Just "Old")

    otherStackRef <- newIORef []
    otherPendingRef <- newIORef mempty
    otherCacheRef <- newIORef initialCache
    otherOutputRef <- newIORef []
    otherInputRef <- newIORef 0
    otherEnv <- mkRuntimeEnv otherStackRef otherPendingRef otherCacheRef otherOutputRef otherInputRef
    crossGeneration <- runRuntime (restore saved) otherEnv
    assert "snapshot crossed a runtime/load generation" (either (const True) (const False) crossGeneration)

    putStrLn "runtime snapshot/cut/I-O regressions passed"
