{-# LANGUAGE CApiFFI #-}
module X.Machine (holVer1) where

import Foreign.Ptr
import Foreign.C.Types

foreign import ccall "hol_v1" c_hol_v1 :: Int -> Ptr (Ptr CChar) -> IO Int

-- holVer1: a wrapper of c_hol_v1
holVer1 :: Int -> [String] -> IO Int
holVer1 = undefined
