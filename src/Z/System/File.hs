module Z.System.File where

import System.IO
import Z.Utils

readFileNow :: FilePath -> IO (Maybe String)
readFileNow = go where
    readNow :: Handle -> IO [String]
    readNow my_handle = do
        my_handle_is_eof <- hIsEOF my_handle
        if my_handle_is_eof
            then return []
            else do
                content <- hGetLine my_handle
                contents <- readNow my_handle
                content `seq` return (content : contents)
    go :: FilePath -> IO (Maybe String)
    go path = do
        my_handle <- openFile path ReadMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsReadable my_handle else return False
        maybe_contents <- if my_handle_is_okay then fmap (callWithStrictArg Just) (readNow my_handle) else return Nothing
        hClose my_handle
        return (fmap unlines maybe_contents)

writeFileNow :: FilePath -> String -> IO Bool
writeFileNow path = go where
    go :: String -> IO Bool
    go content = do
        my_handle <- openFile path WriteMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
        if my_handle_is_okay
            then do
                my_handle << content << Flush
                return ()
            else return ()
        hClose my_handle
        return my_handle_is_okay

drawupFile :: FilePath -> ShowS -> IO Bool
drawupFile path = go where
    go :: ShowS -> IO Bool
    go string_stream = do
        my_handle <- openFile path WriteMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
        if my_handle_is_okay
            then do
                my_handle << string_stream << Flush
                return ()
            else return ()
        hClose my_handle
        return my_handle_is_okay
