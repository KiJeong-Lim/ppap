module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test

testZ :: IO ()
testZ = do
    putStrLn "TEST.testZ> Call (testDoc)."
    testDoc
    putStrLn "TEST.testZ> Eval (testParserBaseProperty)."
    testParserBaseProperty
