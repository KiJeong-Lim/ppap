module Test.Main where

import Z.Text.Doc.Test
import Z.Text.PC.Test

main :: IO ()
main = do
    putStrLn "<<< testDoc"
    testDoc
    putStrLn "<<< mapM testPC [0 .. 6]"
    mapM testPC [0 .. 6]
    putStrLn "<<< testParserBaseProperty"
    testParserBaseProperty
    return ()
