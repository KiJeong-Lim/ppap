{-# LANGUAGE CApiFFI #-}
module X.HigherMachine
    ( Machine
    , Snapshot
    , NativeStep (..)
    , NativeRequest (..)
    , createMachine
    , closeMachine
    , withMachine
    , nextStep
    , nextStepForHost
    , resume
    , setDebugging
    , ensureSymbol
    , reserveUid
    , assign
    , takeSnapshot
    , restoreSnapshot
    , closeSnapshot
    , setWorkLimit
    , getWorkLimit
    ) where

import Control.Concurrent (yield)
import Control.Concurrent.MVar
import Control.Exception (allowInterrupt, bracket, mask_, onException)
import Data.Int
import Data.IORef
import Data.Word
import Foreign.C.String (peekCString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable (sizeOf)

data CMachine
    deriving ()

data Machine
    = Machine (IORef ()) (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

data Snapshot
    = Snapshot (IORef ()) (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

data NativeRequest
    = NativeRequest
        { requestKind :: Int
        , requestHostState :: Word64
        , requestPremises :: Word64
        , requestScope :: Int
        , requestCallId :: Word64
        , requestAuxiliary :: Int64
        , requestTerms :: [Int64]
        , requestState :: [Int64]
        , requestFrames :: [Int64]
        , requestDeclarations :: [Int64]
        }
    deriving (Eq, Show)

data NativeStep
    = Exhausted
    | Answer Word64 [Int64] [Int64]
    | Request NativeRequest
    deriving (Eq, Show)

foreign import ccall safe "hol_v2_create" c_create :: Ptr Int64 -> CSize -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_destroy" c_destroyNow :: Ptr CMachine -> IO ()
foreign import ccall "&hol_v2_destroy" c_destroy :: FinalizerPtr CMachine
foreign import ccall safe "hol_v2_error" c_error :: Ptr CMachine -> IO (Ptr CChar)
foreign import ccall safe "hol_v2_next" c_next :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_answer_size" c_answerSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_answer" c_answer :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_state_size" c_stateSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_state" c_state :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_event_size" c_eventSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_event" c_event :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_event_info" c_eventInfo :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_frames_size" c_framesSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_frames" c_frames :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_declarations_size" c_declarationsSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v2_declarations" c_declarations :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_host_state" c_hostState :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_resume" c_resume :: Ptr CMachine -> CInt -> Word64 -> Word64 -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_assign" c_assign :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v2_set_debugging" c_debug :: Ptr CMachine -> CInt -> IO ()
foreign import ccall safe "hol_v2_ensure_symbol" c_ensureSymbol :: Ptr CMachine -> CSize -> CInt -> IO CInt
foreign import ccall safe "hol_v2_reserve_uid" c_reserveUid :: Ptr CMachine -> IO Word64
foreign import ccall safe "hol_v2_clone" c_clone :: Ptr CMachine -> IO (Ptr CMachine)
foreign import ccall safe "hol_v2_restore" c_restore :: Ptr CMachine -> Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v2_set_work_limit" c_setWorkLimit :: Ptr CMachine -> Word64 -> IO CInt
foreign import ccall safe "hol_v2_work_limit" c_getWorkLimit :: Ptr CMachine -> IO Word64

createMachine :: [Int64] -> IO Machine
createMachine code = mask_ $ withArrayLen code $ \count words -> do
    pointer <- c_create words (fromIntegral count)
    if pointer == nullPtr then
        ioError (userError "Hol V1 native machine allocation failed")
    else do
        owner <- newForeignPtr c_destroy pointer `onException` c_destroyNow pointer
        identity <- newIORef ()
        Machine identity <$> newMVar (Just owner)

closeState :: MVar (Maybe (ForeignPtr CMachine)) -> IO ()
closeState state = modifyMVar_ state $ \current -> do
    maybe (return ()) finalizeForeignPtr current
    return Nothing

closeMachine :: Machine -> IO ()
closeMachine (Machine _ state) = closeState state

withMachine :: [Int64] -> (Machine -> IO a) -> IO a
withMachine code = bracket (createMachine code) closeMachine

withPointer :: MVar (Maybe (ForeignPtr CMachine)) -> (Ptr CMachine -> IO (Either String a)) -> IO (Either String a)
withPointer state action = withMVar state $ \current -> case current of
    Nothing -> return (Left "Hol V1 native machine is closed")
    Just owner -> withForeignPtr owner action

readError :: Ptr CMachine -> IO String
readError pointer = c_error pointer >>= peekCString

setWorkLimit :: Machine -> Word64 -> IO (Either String ())
setWorkLimit (Machine _ state) visits = withPointer state $ \pointer -> do
    result <- c_setWorkLimit pointer visits
    if result < 0 then Left <$> readError pointer else return (Right ())

getWorkLimit :: Machine -> IO (Either String Word64)
getWorkLimit (Machine _ state) = withPointer state (fmap Right . c_getWorkLimit)

copyBuffer :: Ptr CMachine -> (Ptr CMachine -> IO CSize) -> (Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt) -> IO (Either String [Int64])
copyBuffer pointer size copy = do
    count <- size pointer
    if toInteger count > toInteger ((maxBound :: Int) `div` sizeOf (0 :: Int64)) then
        return (Left "Hol V1 native buffer exceeds the host array size")
    else bracket (mallocArray (fromIntegral count)) free $ \output -> do
        status <- copy pointer output count
        if status < 0 then Left <$> readError pointer else Right <$> peekArray (fromIntegral count) output

nextStep :: Machine -> IO (Either String NativeStep)
nextStep = nextStepWith False

nextStepForHost :: Machine -> IO (Either String NativeStep)
nextStepForHost = nextStepWith True

nextStepWith :: Bool -> Machine -> IO (Either String NativeStep)
nextStepWith compact (Machine _ state) = withPointer state $ \pointer -> do
    status <- nextStatus pointer
    case status of
        -1 -> Left <$> readError pointer
        0 -> return (Right Exhausted)
        1 -> do
            answer <- if compact then return (Right []) else copyBuffer pointer c_answerSize c_answer
            current <- copyBuffer pointer c_stateSize c_state
            token <- c_hostState pointer
            return (Answer token <$> answer <*> current)
        3 -> do
            info <- copyBuffer pointer (const (return 6)) c_eventInfo
            terms <- copyBuffer pointer c_eventSize c_event
            current <- copyBuffer pointer c_stateSize c_state
            let debug = case info of
                    Right (4 : _) -> True
                    _ -> False
            frames <- if compact && not debug then return (Right [0]) else copyBuffer pointer c_framesSize c_frames
            declarations <- if compact && not debug then copyBuffer pointer c_declarationsSize c_declarations else return (Right [0])
            return $ do
                fields <- info
                roots <- terms
                bindings <- current
                remaining <- frames
                metadata <- declarations
                case fields of
                    [kind, host, premises, scope, callId, auxiliary]
                        | all (>= 0) [kind, host, premises, scope, callId]
                        , toInteger scope <= toInteger (maxBound :: Int) ->
                            Right (Request (NativeRequest (fromIntegral kind) (fromIntegral host) (fromIntegral premises) (fromIntegral scope) (fromIntegral callId) auxiliary roots bindings remaining metadata))
                    _ -> Left "Hol V1 native machine returned invalid event metadata"
        _ -> return (Left "Hol V1 native machine returned an invalid status")
    where
        nextStatus pointer = do
            status <- c_next pointer
            -- Let signal and timeout threads run even when this loop allocates nothing.
            if status == 2 then yield >> allowInterrupt >> nextStatus pointer else return status

resume :: Machine -> Int -> Word64 -> Word64 -> [Int64] -> IO (Either String ())
resume (Machine _ state) result host premises bindings = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words -> do
        status <- c_resume pointer (fromIntegral result) host premises words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())

setDebugging :: Machine -> Bool -> IO (Either String ())
setDebugging (Machine _ state) enabled = withPointer state $ \pointer -> do
    c_debug pointer (if enabled then 1 else 0)
    return (Right ())

takeSnapshot :: Machine -> IO (Either String Snapshot)
takeSnapshot (Machine identity state) = withPointer state $ \pointer -> mask_ $ do
    duplicate <- c_clone pointer
    if duplicate == nullPtr then
        return (Left "Hol V1 native snapshot allocation failed")
    else do
        owner <- newForeignPtr c_destroy duplicate `onException` c_destroyNow duplicate
        Right . Snapshot identity <$> newMVar (Just owner)

restoreSnapshot :: Machine -> Snapshot -> IO (Either String ())
restoreSnapshot (Machine identity state) (Snapshot source snapshot)
    | identity /= source = return (Left "snapshot belongs to a different runtime")
    | otherwise = withPointer state $ \pointer -> withPointer snapshot $ \saved -> do
        status <- c_restore pointer saved
        if status < 0 then Left <$> readError pointer else return (Right ())

closeSnapshot :: Snapshot -> IO ()
closeSnapshot (Snapshot _ state) = closeState state

ensureSymbol :: Machine -> Int -> Int -> IO (Either String ())
ensureSymbol (Machine _ state) symbol role = withPointer state $ \pointer -> do
    status <- c_ensureSymbol pointer (fromIntegral symbol) (fromIntegral role)
    if status < 0 then Left <$> readError pointer else return (Right ())

reserveUid :: Machine -> IO (Either String Word64)
reserveUid (Machine _ state) = withPointer state $ \pointer -> do
    uid <- c_reserveUid pointer
    if uid == maxBound then Left <$> readError pointer else return (Right uid)

assign :: Machine -> [Int64] -> IO (Either String ())
assign (Machine _ state) bindings = withPointer state $ \pointer ->
    withArrayLen bindings $ \count words -> do
        status <- c_assign pointer words (fromIntegral count)
        if status < 0 then Left <$> readError pointer else return (Right ())
