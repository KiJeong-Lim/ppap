module Jasmine.Alpha1.Header.TermNode.Test where

import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.TermNode.DeBruijn
import Jasmine.Alpha1.Header.Util

getTermNodeUnit :: Int -> String
getTermNodeUnit 0 = "\\x1 -> x1 x1"
getTermNodeUnit 1 = "\\x1 -> (\\x2 -> x2 x2) x1"
getTermNodeUnit 2 = "\\x1 -> \\x2 -> (\\x3 -> x3 x1) x2"
getTermNodeUnit 3 = "\\x1 -> \\x2 -> fix x3 := (\\x4 -> x2) x3"
getTermNodeUnit 4 = "fix x1 := \\x2 -> x2"
getTermNodeUnit _ = undefined

rewriteTest :: Int -> IO ()
rewriteTest object_no = do
    let object_rep = getTermNodeUnit object_no
        object = readLambdaTerm object_rep
        eval1 = toDeBruijn . evalLambdaTerm NF
        eval2 = rewrite NF . toDeBruijn
        object1 = eval1 object
        object2 = eval2 object
    putStrLn (if object1 == object2 then ">>> Test passed:" else ">>> Test failed:")
    putStrLn ("    EVAL1[ " ++ object_rep ++ " ] = " ++ shows object1 "")
    putStrLn ("    EVAL2[ " ++ object_rep ++ " ] = " ++ shows object2 "")
    return ()
