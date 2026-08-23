module Z.System.File
    ( readFileNow
    , writeFileNow
    ) where

import Control.Exception (IOException, catch, evaluate)
import System.Directory
import System.IO
import Z.Utils

readFileNow :: FilePath -> IO (Maybe String)
readFileNow file = readNow `catch` unreadable where
    unreadable :: IOException -> IO (Maybe String)
    unreadable _ = return Nothing
    readNow = do
        exists <- doesFileExist file
        if exists then do
            file_permission <- getPermissions file
            if readable file_permission then do
                withFile file ReadMode $ \handle -> do
                    hSetNewlineMode handle noNewlineTranslation
                    okay <- hIsReadable handle
                    if okay then do
                        content <- hGetContents handle
                        -- Force the lazy contents before `withFile' closes the handle.
                        -- In particular, do not reconstruct the input with `hGetLine':
                        -- doing so invents a newline after a non-terminated final line.
                        _ <- evaluate (length content)
                        return (Just content)
                    else
                        return Nothing
            else
                return Nothing
        else
            return Nothing

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow file_dir my_content = do
    my_handle <- openFile file_dir WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    if my_handle_is_okay then do
        my_handle << my_content << Flush
        hClose my_handle
        return True
    else do
        hClose my_handle
        return False
