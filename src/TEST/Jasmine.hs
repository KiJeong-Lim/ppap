module TEST.Jasmine where

import Jasmine.Alpha1.Solver.Presburger.Test (testPresburger)
import Z.System.Shelly (shelly)

testJasmine :: IO ()
testJasmine = do
    query <- shelly ("TEST.testJasmine =<< ")
    case query of
        "Presburger" -> do
            shelly ("TEST.testJasmine >>= eval (TEST.testJasmine.testPresburger)")
            testPresburger
            return ()
        invalid_query -> do
            shelly ("TEST.testJasmine >>= tell (invalid-query=" ++ shows invalid_query ")")
            return ()
    shelly ("TEST.testJasmine >>= quit")
    return ()
