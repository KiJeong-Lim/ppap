module Main where

import Control.Monad (unless)
import Data.List (isInfixOf)
import Hol.BETA.Diagnostic
import Hol.BETA.Header (SLoc (..))
import System.Exit (exitFailure)
import qualified Z.Doc as Doc

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("diagnostic regression failed: " ++ label)
    exitFailure

main :: IO ()
main = do
    let rendered = diagnosticWith DiagnosticTest "HolBETA-Multiline" (Just ["abcdef", "ghijkl", "mnopqr"]) (SLoc (1, 3) (3, 4)) [Doc.text "multiline span"]
    assert "header lost the complete source span" (isInfixOf "1:3-3:4: error: [HolBETA-Multiline]" rendered)
    assert "first source row was not rendered" (isInfixOf "1 | abcdef" rendered)
    assert "middle source row was not rendered" (isInfixOf "2 | ghijkl" rendered)
    assert "last source row was not rendered" (isInfixOf "3 | mnopqr" rendered)
    assert "DiagnosticTest emitted ANSI color escapes" (not (isInfixOf "\ESC[" rendered))

    let sourceLess = diagnosticWith DiagnosticTest "HolBETA-NoSource" Nothing (SLoc (1, 3) (3, 4)) [Doc.text "source-less span"]
    assert "source-less multiline span omitted row/start carets"
        (isInfixOf "1 | \n  |   ^\n2 | \n  | ^\n3 | \n  | ^^^^" sourceLess)

    let tabbed = diagnosticWith DiagnosticTest "HolBETA-Tab" (Just ["a\tb"]) (SLoc (1, 3) (1, 3)) [Doc.text "tabbed prefix"]
    assert "caret indentation did not preserve a source tab"
        (isInfixOf "1 | a\tb\n   |  \t^" tabbed)

    assert "single-line EOF position was not the cursor after the last code point"
        (eofSLoc "abc" == SLoc (1, 4) (1, 4))
    assert "EOF after a final newline was not the next row at column one"
        (eofSLoc "abc\nxy\n" == SLoc (3, 1) (3, 1))
    let eofRendered = diagnosticWith DiagnosticTest "HolBETA-EOF" (Just ["abc", "xy"]) (eofSLoc "abc\nxy") [Doc.text "EOF span"]
    assert "rendered EOF diagnostic lost its cursor location"
        (isInfixOf "2:3-2:3: error: [HolBETA-EOF]" eofRendered)
    putStrLn "multiline/source-less/tab/EOF diagnostic regressions passed"
