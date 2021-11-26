module Calc.ControlSystem.Export where

import Calc.ControlSystem.Diagram.Solver
import Calc.ControlSystem.Util
import qualified Data.Map.Strict as Map
import Z.Math.Classes
import Z.Math.V1
import Z.System.File

interpreteSystem :: System -> MyExpr
interpreteSystem sys = reduceElemExpr ReduceLv2 (makePathTable (_entry_point sys) (_get_diagram sys) Map.! (_main_output sys))

readSystem :: FilePath -> IO (Maybe System)
readSystem file_dir = undefined
