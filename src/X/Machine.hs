{-# LANGUAGE CApiFFI #-}
module X.Machine (Machine, createMachine, closeMachine, withMachine, nextAnswer) where

import Control.Concurrent (yield)
import Control.Concurrent.MVar
import Control.Exception (allowInterrupt, bracket, mask_, onException)
import Data.Int (Int64)
import Foreign.C.String (peekCString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc (free)
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.Storable (sizeOf)

data CMachine
    deriving ()

newtype Machine = Machine (MVar (Maybe (ForeignPtr CMachine)))
    deriving ()

foreign import ccall safe "hol_v1_create" c_create :: Ptr Int64 -> CSize -> IO (Ptr CMachine)
foreign import ccall safe "hol_v1_next" c_next :: Ptr CMachine -> IO CInt
foreign import ccall safe "hol_v1_answer_size" c_answerSize :: Ptr CMachine -> IO CSize
foreign import ccall safe "hol_v1_answer" c_answer :: Ptr CMachine -> Ptr Int64 -> CSize -> IO CInt
foreign import ccall safe "hol_v1_error" c_error :: Ptr CMachine -> IO (Ptr CChar)
foreign import ccall safe "hol_v1_destroy" c_destroyNow :: Ptr CMachine -> IO ()
foreign import ccall "&hol_v1_destroy" c_destroy :: FinalizerPtr CMachine

createMachine :: [Int64] -> IO Machine
createMachine code = mask_ $ withArrayLen code $ \count words -> do
    pointer <- c_create words (fromIntegral count)
    if pointer == nullPtr then
        ioError (userError "Hol V1 machine allocation failed")
    else do
        owner <- newForeignPtr c_destroy pointer `onException` c_destroyNow pointer
        Machine <$> newMVar (Just owner)

closeMachine :: Machine -> IO ()
closeMachine (Machine state) = modifyMVar_ state $ \current -> do
    maybe (return ()) finalizeForeignPtr current
    return Nothing

withMachine :: [Int64] -> (Machine -> IO a) -> IO a
withMachine code = bracket (createMachine code) closeMachine

nextAnswer :: Machine -> IO (Either String (Maybe [Int64]))
nextAnswer (Machine state) = withMVar state $ \current -> case current of
    Nothing -> return (Left "Hol V1 machine is closed")
    Just owner -> withForeignPtr owner $ \pointer -> do
        status <- nextStatus pointer
        if status < 0 then
            Left <$> readError pointer
        else if status == 0 then
            return (Right Nothing)
        else do
            count <- c_answerSize pointer
            if toInteger count > toInteger ((maxBound :: Int) `div` sizeOf (0 :: Int64)) then
                return (Left "Hol V1 answer exceeds the host array size")
            else bracket (mallocArray (fromIntegral count)) free $ \output -> do
                copied <- c_answer pointer output count
                if copied < 0 then
                    Left <$> readError pointer
                else
                    Right . Just <$> peekArray (fromIntegral count) output
    where
        nextStatus pointer = do
            status <- c_next pointer
            -- Let signal and timeout threads run even when this loop allocates nothing.
            if status == 2 then yield >> allowInterrupt >> nextStatus pointer else return status
        readError pointer = c_error pointer >>= peekCString
