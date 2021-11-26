module Calc.Runtime.Executor where

import Calc.ControlSystem.Export
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO
import Z.Text.Doc
import Z.Text.PM
import Z.System.File
import Z.System.Path
import Z.Utils

runCalc :: FilePath -> IO ()
runCalc filedir = return ()
