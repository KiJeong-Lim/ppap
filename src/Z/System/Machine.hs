{-# LANGUAGE ForeignFunctionInterface #-}
module Z.System.Machine where

import qualified Foreign.C.Error as C
import qualified Foreign.C.String as C
import qualified Foreign.C.Types as C

foreign import ccall "runMachine" c_runMachine :: C.CString -> IO C.CInt

runMachine :: String -> IO Integer
runMachine str = do
    exit_code <- C.withCString str c_runMachine
    return (toInteger exit_code)
