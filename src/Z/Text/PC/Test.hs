module Z.Text.PC.Test where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Text.PC
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

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

instance Show (ParserBase chr val) where
    showsPrec prec = const id
    showList = const id

instance (Show chr, Arbitrary chr, EqProp val, EqProp chr) => EqProp (ParserBase chr val) where
    p1 =-= p2 = runPB p1 =-= runPB p2

instance Arbitrary val => Arbitrary (MyPC val) where
    arbitrary = fmap MyPC arbitrary
    shrink = map MyPC . shrink . unMyPC

instance EqProp val => EqProp (MyPC val) where
    p1 =-= p2 = unMyPC p1 =-= unMyPC p2

checkParserBaseIsMonad :: TestBatch
checkParserBaseIsMonad = ("check-`ParserBase'-is-`Moand'", map (fmap (withMaxSuccess 100)) (snd (go undefined))) where
    go :: ParserBase Char (Int, Int, Int) -> TestBatch
    go = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = ("check-`ParserBase'-is-`MoandPlus'", map (fmap (withMaxSuccess 10000)) (snd (go undefined))) where
    go :: ParserBase Char (Int, Int) -> TestBatch
    go = monadPlus

testParserBase :: IO ()
testParserBase = do
    quickBatch checkParserBaseIsMonad
    quickBatch checkParserBaseIsMonadPlus
    return ()

testPC :: Int -> IO ()
testPC n = putStrLn (either id show (zipWith (execPC (mkFPath "Z\\Text\\PC\\Test.hs")) getTestPC getTestInput !! n)) where
    getTestPC :: [PC String]
    getTestPC =
        [ pure (++) <*> regexPC "\"abc\"" <*> regexPC "\"defg \""
        , regexPC "\"abcdefg \""
        , regexPC "['0'-'9']*" <* skipWhite
        , regexPC "(['0'-'9']* \" \"*)*"
        , acceptQuote
        , acceptQuote
        , acceptQuote
        , undefined
        , undefined
        ]
    getTestInput :: [String]
    getTestInput =
        [ "abcdefg"
        , "abcdefg  "
        , "01234      "
        , "01 2  3   4"
        , "\"hello\"\\\""
        , "\"'\""
        , "\"\\'\""
        , undefined
        , undefined
        ]
