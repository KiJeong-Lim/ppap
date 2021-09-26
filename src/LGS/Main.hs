module LGS.Main where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
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
import Y.Base
import Z.Text.PC
import Z.Utils

runLGS :: FilePath -> IO ()
runLGS dir = do
    x_src <- readFile dir
    case runPC (FPath dir) (many (readBlock <* many lend) <* eofPC) x_src of
        Left err -> putStrLn err
        Right xblocks -> case runIdentity (runExceptT (genLexer xblocks)) of
            Left err -> do
                writeFile (dir ++ ".failed") err
                shelly "LGS >>= said (generating-failed)"
            Right delta -> do
                writeFile (dir ++ ".hs") (delta "")
                shelly "LGS >>= said (the-lexer-has-been-generated)"

main :: IO ()
main = do
    shelly "LGS =<< "
    dir <- getLine
    runLGS dir
    shelly "LGS >>= quit"
