module TEST.Z where

import Z.Text.Doc.Test
import Z.Text.PC.Test

testZ :: IO ()
testZ = do
    putStrLn "TEST> testDoc"
    testDoc
    putStrLn "TEST> mapM testPC [0 .. 6]"
    mapM testPC [0 .. 6]
    putStrLn "TEST> testParserBaseProperty"
    testParserBaseProperty
    return ()
