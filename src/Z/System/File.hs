module Z.System.File where

import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import System.IO
import Z.Utils

readFileNow :: FilePath -> IO (Maybe String)
readFileNow path = do
    my_handle <- openFile path ReadMode
    my_handle_is_open <- hIsOpen my_handle
    my_result <- runMaybeT $ do
        my_handle_is_okay <- if my_handle_is_open then lift (hIsReadable my_handle) else return False
        if my_handle_is_okay
            then do
                my_content <- fix $ \get_content -> do
                    let my_append = foldr (\ch -> \kont -> callWithStrictArg (kons ch . kont)) id
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

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow path my_content = do
    my_handle <- openFile path WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    if my_handle_is_okay
        then do
            my_handle << my_content << Flush
            return ()
        else return ()
    my_result <- if my_handle_is_okay then hIsWritable my_handle else return False
    my_result `seq` hClose my_handle
    return my_result
