module Z.Text.PC.Test where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Text.PC
import Z.Text.PC.Base

instance (CoArbitrary chr, Arbitrary chr, Arbitrary val) => Arbitrary (ParserBase chr val) where
    arbitrary = choose (0, 10) >>= go where
        go :: (CoArbitrary chr, Arbitrary chr, Arbitrary val) => Int -> Gen (ParserBase chr val)
        go rank
            | rank > 0 = oneof
                [ go (rank - 1)
                , pure PAct <*> liftArbitrary (go (rank - 1))
                , pure PAlt <*> (choose (0, 5) >>= flip vectorOf (pure (,) <*> go (rank - 1) <*> (choose (0, 5) >>= flip vectorOf arbitrary)))
                ]
            | otherwise = pure PVal <*> arbitrary
    shrink = const []

instance (Show chr, Arbitrary chr, EqProp val, EqProp chr) => EqProp (ParserBase chr val) where
    parser1 =-= parser2 = runPB parser1 =-= runPB parser2

checkParserBaseIsMonad :: TestBatch
checkParserBaseIsMonad = go undefined where
    go :: ParserBase Char (Int, Int, Int) -> TestBatch
    go = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = go undefined where
    go :: ParserBase Char (Int, Int) -> TestBatch
    go = monadPlus

testParserBase :: IO ()
testParserBase = do
    quickBatch checkParserBaseIsMonad
    quickBatch checkParserBaseIsMonadPlus
    return ()

testPC :: Int -> String
testPC n = either id show (zipWith runPC getTestPC getTestInput !! n) where
    getTestPC :: [PC String]
    getTestPC =
        [ regexPC "['a'-'z']"
        , regexPC "['0'-'9']*"
        , regexPC "['0'-'9']*" <* skipWhite
        ]
    getTestInput :: [String]
    getTestInput =
        [ "abcdefg"
        , "01234"
        , "01234      "
        ]
