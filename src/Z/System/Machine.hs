{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Z.System.Machine where
{-
import qualified Foreign.C as C

foreign import ccall "myread" c_myread :: IO C.CString

gets :: IO String
gets = c_myread >>= C.peekCString
-}