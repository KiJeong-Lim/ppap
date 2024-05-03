module LGS.Main where

import Control.Applicative
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LGS.Read
import LGS.Show
import LGS.Util
import Z.System.File
import Z.System.Shelly
import Z.Text.PC
import Z.Utils

main :: IO ()
main = do
    dir <- shelly ("LGS =<< ")
    let dir_rev = reverse dir
    let dir' = if take 4 dir_rev == "txt." then reverse (drop 4 dir_rev) else dir
    x_src <- readFileNow dir
    case maybe (Left ("cannot open file: " ++ dir)) (runPC dir (many (readBlock <* many lend) <* eofPC)) x_src of
        Left err -> putStrLn err
        Right xblocks -> case runIdentity (runExceptT (genLexer xblocks)) of
            Left err -> do
                writeFileNow (dir' ++ ".failed") err
                shelly ("LGS >>= tell (generating-failed)")
                return ()
            Right delta -> do
                writeFileNow (dir' ++ ".hs") delta
                shelly ("LGS >>= tell (the-lexer-has-been-generated)")
                return ()
