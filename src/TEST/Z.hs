module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test
import Z.Utils

testZ :: IO ()
testZ = do
    shelly "TEST.testZ> call (testDoc)."
    testDoc
    shelly "TEST.testZ> eval (testParserBaseProperty)."
    testParserBaseProperty
