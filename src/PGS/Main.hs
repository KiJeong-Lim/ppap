module PGS.Main where

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
import PGS.Read
import PGS.Show
import PGS.Util
import Y.Base
import Z.Text.PC
import Z.Utils

runPGS :: FilePath -> IO ()
runPGS dir = do
    y_src <- readFile dir
    case runPC (FPath dir) (many (readBlock <* many lend) <* eofPC) y_src of
        Left err -> putStrLn err
        Right yblocks -> case runIdentity (runExceptT (genParser yblocks)) of
            Left err -> do
                writeFile (dir ++ ".failed") err
                shelly "PGS >>= tell (generating-failed)"
            Right delta -> do
                writeFile (dir ++ ".hs") (delta "")
                shelly "PGS >>= tell (the-parser-has-been-generated)"

main :: IO ()
main = do
    shelly "PGS =<< "
    dir <- getLine
    runPGS dir
    shelly "PGS >>= quit"
