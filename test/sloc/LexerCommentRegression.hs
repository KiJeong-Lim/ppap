module Main where

import Control.Monad (unless)
import qualified Data.Set as Set
import qualified Hol.ALPHA2.Header as AlphaHeader
import qualified Hol.ALPHA2.PlanHolLexer as Alpha
import qualified Hol.BETA.Header as BetaHeader
import qualified Hol.BETA.PlanHolLexer as Beta
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("lexer comment regression failed: " ++ label)
    exitFailure

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

isLeftAt :: Eq a => a -> Either a b -> Bool
isLeftAt expected (Left actual) = actual == expected
isLeftAt _ _ = False

betaTrueBeginsAt :: (Int, Int) -> Either a [Beta.Token] -> Bool
betaTrueBeginsAt expected (Right (Beta.T_true loc : _)) = BetaHeader._BegPos loc == expected
betaTrueBeginsAt _ _ = False

alphaTrueBeginsAt :: (Int, Int) -> Either a [Alpha.Token] -> Bool
alphaTrueBeginsAt expected (Right (Alpha.T_true loc : _)) = AlphaHeader._BegPos loc == expected
alphaTrueBeginsAt _ _ = False

alphaQuotedId :: String -> Either a [Alpha.Token] -> Bool
alphaQuotedId expected (Right [Alpha.T_id _ actual]) = actual == expected
alphaQuotedId _ _ = False

main :: IO ()
main = do
    assert "BETA accepted an unterminated block comment"
        (isLeftAt (1, 1) (Beta.runHolLexer "(* unterminated"))
    assert "ALPHA2 accepted an unterminated block comment"
        (isLeftAt (1, 1) (Alpha.runHolLexer "(* unterminated"))
    assert "BETA lost the opening delimiter location"
        (isLeftAt (2, 3) (Beta.runHolLexer "true.\n  (* unterminated"))
    assert "ALPHA2 lost the opening delimiter location"
        (isLeftAt (2, 3) (Alpha.runHolLexer "true.\n  (* unterminated"))

    assert "comment opener inside a BETA string was misclassified"
        (isRight (Beta.runHolLexer "\"(*\""))
    assert "comment opener inside an ALPHA2 string was misclassified"
        (isRight (Alpha.runHolLexer "\"(*\""))
    assert "comment opener inside a BETA line comment was misclassified"
        (isRight (Beta.runHolLexer "% (* ignored\ntrue."))
    assert "comment opener inside an ALPHA2 line comment was misclassified"
        (isRight (Alpha.runHolLexer "% (* ignored\ntrue."))

    -- The first closer ends a block comment.  A nested-looking opener is
    -- ordinary comment payload, consistently with the generated DFAs.
    assert "BETA block comments unexpectedly became nesting"
        (isRight (Beta.runHolLexer "(* outer (* inner *) true."))
    assert "ALPHA2 block comments unexpectedly became nesting"
        (isRight (Alpha.runHolLexer "(* outer (* inner *) true."))

    assert "BETA did not accept exactly space/tab/CR/LF whitespace"
        (betaTrueBeginsAt (2, 1) (Beta.runHolLexer " \t\r\ntrue."))
    assert "ALPHA2 did not accept exactly space/tab/CR/LF whitespace"
        (alphaTrueBeginsAt (2, 1) (Alpha.runHolLexer " \t\r\ntrue."))
    assert "BETA treated vertical tab as lexical whitespace"
        (isLeftAt (1, 1) (Beta.runHolLexer "\vtrue."))
    assert "ALPHA2 treated vertical tab as lexical whitespace"
        (isLeftAt (1, 1) (Alpha.runHolLexer "\vtrue."))
    assert "BETA treated form feed as lexical whitespace"
        (isLeftAt (1, 1) (Beta.runHolLexer "\ftrue."))
    assert "ALPHA2 treated form feed as lexical whitespace"
        (isLeftAt (1, 1) (Alpha.runHolLexer "\ftrue."))

    mapM_ (\name -> assert
            ("ALPHA2 did not decode quoted reserved identifier " ++ show name)
            (alphaQuotedId name (Alpha.runHolLexer ("`" ++ name ++ "`"))))
        (Set.toList AlphaHeader.reservedNamedIdentifiers)

    putStrLn "BETA/ALPHA2 lexer-policy regressions passed"
