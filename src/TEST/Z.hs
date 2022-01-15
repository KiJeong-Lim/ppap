module TEST.Z where

import Z.System.Shelly
import Z.Text.Doc.Test
import Z.Text.PC.Test
import Z.Utils

testZ :: IO ()
testZ = do
    shelly ("TEST.testZ >>= eval (testDoc)")
    putStrLn ""
    testDoc
    putStrLn ""
    shelly ("TEST.testZ >>= eval (testParserBaseProperty)")
    testParserBaseProperty
    putStrLn ""
    shelly ("TEST.testZ >>= quit")
    return ()
