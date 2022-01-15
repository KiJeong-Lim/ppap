module Z.System.File
    ( readFileNow
    , writeFileNow
    ) where

import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import System.Directory
import System.IO
import Z.Utils

when :: Monad m => m Bool -> m a -> m (Maybe a)
when condm actionm = do
    cond <- condm
    if cond then fmap Just actionm else return Nothing

readFileNow :: FilePath -> IO (Maybe String)
readFileNow file = do
    tmp <- when (doesFileExist file) $ do
        file_permission <- getPermissions file
        if readable file_permission
            then do
                my_handle <- openFile file ReadMode
                my_handle_is_open <- hIsOpen my_handle
                my_result <- runMaybeT $ do
                    my_handle_is_okay <- if my_handle_is_open then lift (hIsReadable my_handle) else return False
                    if my_handle_is_okay
                        then do
                            my_content <- fix $ \get_content -> do
                                let my_append = foldr (fmap . kons) id
                                my_handle_is_eof <- lift (hIsEOF my_handle)
                                if my_handle_is_eof
                                    then return ""
                                    else do
                                        content1 <- lift (hGetLine my_handle)
                                        my_handle_is_still_okay <- lift (hIsReadable my_handle)
                                        content2 <- if my_handle_is_still_okay then get_content else fail ""
                                        return (my_append content1 (my_append "\n" content2))
                            callWithStrictArg return my_content
                        else fail ""
                my_result `seq` hClose my_handle
                return my_result
        else return Nothing
    callWithStrictArg return (maybe Nothing id tmp)

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow file_dir my_content = do
    my_handle <- openFile file_dir WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    if my_handle_is_okay
        then do
            my_handle << my_content << Flush
            hClose my_handle
            return True
        else do
            hClose my_handle
            return False
