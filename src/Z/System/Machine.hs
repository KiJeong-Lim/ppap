{-# LANGUAGE ForeignFunctionInterface #-}
module Z.System.Machine where

import qualified Foreign.C as C

foreign import ccall "runMachine" c_runMachine :: C.CString -> IO C.CInt

runMachine :: String -> IO Integer
runMachine str = fmap toInteger (C.withCString str c_runMachine)
