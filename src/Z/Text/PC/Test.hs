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
            | rank > 0 = frequency
                [ (8, go (rank - 1))
                , (2, pure PAct <*> liftArbitrary (choose (0, 5) >>= flip vectorOf (pure (,) <*> go (rank - 1) <*> (choose (0, 5) >>= flip vectorOf arbitrary))))
                ]
            | otherwise = pure PVal <*> arbitrary
    shrink = const []

instance Show (ParserBase chr val) where
    showsPrec prec = const id

instance (Show chr, Arbitrary chr, EqProp val, EqProp chr) => EqProp (ParserBase chr val) where
    p1 =-= p2 = execPB p1 =-= execPB p2

instance Arbitrary val => Arbitrary (MyPC val) where
    arbitrary = fmap MyPC arbitrary
    shrink = map MyPC . shrink . unMyPC

instance EqProp val => EqProp (MyPC val) where
    p1 =-= p2 = execPC p1 =-= execPC p2

checkParserBaseIsMonad :: TestBatch
checkParserBaseIsMonad = ("check-`ParserBase'-is-`Monad'", map (fmap (withMaxSuccess 1000000)) (snd (go undefined))) where
    go :: PB LocChr (Int, Int, Int) -> TestBatch
    go = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = ("check-`ParserBase'-is-`MonadPlus'", map (fmap (withMaxSuccess 1000000)) (snd (go undefined))) where
    go :: PB LocChr (Int, Int) -> TestBatch
    go = monadPlus

testParserBaseProperty :: IO ()
testParserBaseProperty = do
    quickBatch checkParserBaseIsMonad -- failed=[]
    quickBatch checkParserBaseIsMonadPlus -- failed=["left  identity", "right identity"]
    return ()

testPC :: Int -> IO ()
testPC n = putStrLn (either id show (zipWith (runPC (mkFPath "Z\\Text\\PC\\Test.hs")) getTestPC getTestInput !! n)) where
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
        , undefined
        ]
