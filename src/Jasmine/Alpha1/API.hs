module Jasmine.Alpha1.API
    ( runJasmineAlpha1
    ) where

import Jasmine.Alpha1.Analyzer.Export
import Jasmine.Alpha1.Compiler.Export
import Jasmine.Alpha1.Desugarer.Export
import Jasmine.Alpha1.Header.Export
import Jasmine.Alpha1.Interpreter.Export
import Jasmine.Alpha1.TypeChecker.Export

runJasmineAlpha1 :: IO ()
runJasmineAlpha1 = return ()
