module Main (main) where

import Control.Applicative (many)
import Control.Monad.Trans.Except
import Data.Functor.Identity
import qualified LGS.Alpha1 as Legacy
import qualified LGS.Alpha2 as Current
import System.Environment (getArgs)
import System.FilePath ((</>))
import Z.OldPC (eofPC, lend, runPC)

lexerSpec :: [String] -> [String] -> String
lexerSpec rules checks = unlines $
    [ "\\hshead {"
    , "    module Main (main) where"
    , "    import Control.Monad (unless)"
    , "}"
    , "\\target {"
    , "    token-type: \"(String, String, (Int, Int), (Int, Int))\""
    , "    lexer-name: \"scan\""
    , "}"
    ] ++ rules ++
    [ "\\hstail {"
    , "    assert label okay = unless okay (fail label)"
    , "    main = do"
    ] ++ map ("        " ++) checks ++ ["}"]

match :: String -> String -> [String]
match pattern label = ["\\xmatch " ++ pattern ++ ":", "    (" ++ show label ++ ", this, (row1, col1), (row2, col2))"]

ordinarySpec :: String
ordinarySpec = lexerSpec rules checks where
    rules = concat
        [ match "\"ab\"" "first"
        , match "\"ab\"" "second"
        , match "\"abcdefx\"" "long"
        , match "\"abc\"" "short"
        , match "\"a\"" "a"
        , match "['b' 'c' 'd' 'e' 'f' 'g' 'x']" "rest"
        , match "['\\t']" "tab"
        , ["\\xmatch [' ' '\\n']+: skip"]
        , match "['z']+" "long-run"
        ]
    checks =
        [ "assert \"first rule wins equal-length matches\" (scan \"ab\" == Right [(\"first\", \"ab\", (1,1), (1,2))])"
        , "assert \"longest match wins\" (scan \"abcdefx\" == Right [(\"long\", \"abcdefx\", (1,1), (1,7))])"
        , "let rollback = [(\"short\", \"abc\", (1,1), (1,3))] ++ [(\"rest\", [ch], (1,col), (1,col)) | (ch,col) <- zip \"def\" [4..]]"
        , "assert \"restore nonaccepting suffix at EOF\" (scan \"abcdef\" == Right rollback)"
        , "assert \"restore nonaccepting suffix at failed transition\" (scan \"abcdefg\" == Right (rollback ++ [(\"rest\", \"g\", (1,7), (1,7))]))"
        , "assert \"explicit tab and positions after skipped whitespace\" (scan \" \\n\\tab\" == Right [(\"tab\", \"\\t\", (2,1), (2,1)), (\"first\", \"ab\", (2,2), (2,3))])"
        , "assert \"error location after accepted token\" (scan \"ab?\" == Left (1,3))"
        , "let longToken = replicate 200000 'z'"
        , "assert \"long token contents and position\" (scan longToken == Right [(\"long-run\", longToken, (1,1), (1,200000))])"
        , "putStrLn \"lexer generation, rollback, tab and long-token regressions passed\""
        ]

trailingSpec :: String
trailingSpec = lexerSpec rules checks where
    rules = concat
        [ match "\"a\"+ / \"b\"+" "before"
        , match "\"b\"+" "after"
        , ["\\xmatch [' ' '\\n']+: skip"]
        ]
    checks =
        [ "assert \"trailing context is returned to the input\" (scan \"aaabbb\" == Right [(\"before\", \"aaa\", (1,1), (1,3)), (\"after\", \"bbb\", (1,4), (1,6))])"
        , "assert \"trailing context preserves locations\" (scan \"\\naaabb\" == Right [(\"before\", \"aaa\", (2,1), (2,3)), (\"after\", \"bb\", (2,4), (2,5))])"
        , "assert \"missing trailing context fails\" (scan \"aaa\" == Left (1,1))"
        , "putStrLn \"lexer trailing-context regressions passed\""
        ]

writeGenerated :: FilePath -> Either String [String] -> IO ()
writeGenerated path = either fail (writeFile path . concat)

main :: IO ()
main = do
    [directory] <- getArgs
    legacy <- either fail return (runPC "legacy lexer" (many (Legacy.readBlock <* many lend) <* eofPC) ordinarySpec)
    writeGenerated (directory </> "LegacyLexer.hs") (runIdentity (runExceptT (Legacy.genLexer legacy)))
    current <- either fail return (runPC "current lexer" (many (Current.readBlock <* many lend) <* eofPC) ordinarySpec)
    writeGenerated (directory </> "CurrentLexer.hs") (runIdentity (runExceptT (Current.genLexer current)))
    trailing <- either fail return (runPC "trailing context lexer" (many (Current.readBlock <* many lend) <* eofPC) trailingSpec)
    writeGenerated (directory </> "TrailingLexer.hs") (runIdentity (runExceptT (Current.genLexer trailing)))
