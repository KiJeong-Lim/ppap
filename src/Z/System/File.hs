module Z.System.File where

import System.IO

readFileNow :: FilePath -> IO (Maybe String)
readFileNow = go where
    readNow :: Handle -> IO [String]
    readNow my_handle = do
        my_handle_is_eof <- hIsEOF my_handle
        if my_handle_is_eof
            then do
                content <- hGetLine my_handle
                contents <- readNow my_handle
                content `seq` return (content : contents)
            else return []
    go :: FilePath -> IO (Maybe String)
    go path = do
        my_handle <- openFile path ReadMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsReadable my_handle else return False
        res <- if my_handle_is_okay
            then do
                contents <- readNow my_handle
                let content = unlines contents
                content `seq` return (Just content)
            else return Nothing
        hClose my_handle
        return res

writeFileNow :: FilePath -> String -> IO Bool
writeFileNow = go where
    writeNow :: Handle -> [String] -> IO ()
    writeNow my_handle [] = return ()
    writeNow my_handle (content : contents) = do
        hPutStrLn my_handle content
        writeNow my_handle contents
    go :: FilePath -> String -> IO Bool
    go path content = do
        my_handle <- openFile path WriteMode
        my_handle_is_open <- hIsOpen my_handle
        my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
        if my_handle_is_okay then writeNow my_handle (lines content) else return ()
        hClose my_handle
        return my_handle_is_okay
