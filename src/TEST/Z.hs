module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test
import Z.Utils

testZ :: IO ()
testZ = do
    shelly "TEST.testZ >>= eval (testDoc)"
    testDoc
    shelly "TEST.testZ >>= eval (testParserBaseProperty)"
    testParserBaseProperty
    shelly "TEST.testZ >>= quit"
