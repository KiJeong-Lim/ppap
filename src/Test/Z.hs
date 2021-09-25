module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test

testZ :: IO ()
testZ = do
    putStrLn "TEST.testZ> Call (testDoc).\n"
    testDoc
    putStrLn "TEST.testZ> Eval (testParserBaseProperty).\n"
    testParserBaseProperty
    putStrLn "TEST.testZ> Quit.\n"
