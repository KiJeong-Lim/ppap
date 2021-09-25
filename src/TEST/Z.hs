module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test

testZ :: IO ()
testZ = do
    putStrLn "TEST.testZ> call (testDoc)."
    testDoc
    putStrLn "TEST.testZ> eval (testParserBaseProperty)."
    testParserBaseProperty
