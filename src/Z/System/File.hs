module Z.System.File where

import Control.Monad
import System.IO
import Z.Utils

readFileNow :: FilePath -> IO (Maybe String)
readFileNow = go where
    readContentNow :: Handle -> IO [String]
    readContentNow my_handle = do
        my_handle_is_eof <- hIsEOF my_handle
        if my_handle_is_eof
            then return []
            else do
                content <- hGetLine my_handle
                contents <- readContentNow my_handle
                content `seq` return (content : contents)
    go :: FilePath -> IO (Maybe String)
    go path = do
        my_handle <- openFile path ReadMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsReadable my_handle else return False
        if my_handle_is_okay
            then do
                contents <- readContentNow my_handle
                callWithStrictArg (return . Just) (unlines contents)
            else return Nothing

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow path content = do
    my_handle <- openFile path WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    when my_handle_is_okay $ do
        my_handle << content << Flush
        return ()
    well_printed <- if my_handle_is_okay then hIsWritable my_handle else return False
    hClose my_handle
    return well_printed
