module Z.Text.PC.Test where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Text.PC
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

instance (Arbitrary chr, CoArbitrary chr, Arbitrary val) => Arbitrary (ParserBase chr val) where
    arbitrary = choose (0, 10) >>= go where
        go :: (Arbitrary chr, CoArbitrary chr, Arbitrary val) => Int -> Gen (ParserBase chr val)
        go rank
            | rank > 0 = frequency
                [ (8, go (rank - 1))
                , (2, pure PAct <*> genPAct (go (rank - 1)))
                ]
            | otherwise = pure PVal <*> arbitrary
        genPAct :: (Arbitrary chr, CoArbitrary chr) => Gen (ParserBase chr val) -> Gen ([chr] -> [(ParserBase chr val, [chr])])
        genPAct seed = do
            conds <- listOf arbitrary
            p <- seed
            return (parsing p conds)
        parsing :: val -> [chr -> Bool] -> ([chr] -> [(val, [chr])])
        parsing val [] str = [(val, str)]
        parsing val (cond : conds) (ch : str) = if cond ch then parsing val conds str else []
        parsing val _ _ = []
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
checkParserBaseIsMonad = ("check \"Monad ParserBase\"", map (fmap (withMaxSuccess 1000000)) (snd (go undefined))) where
    go :: PB LocChr (Int, Int, Int) -> TestBatch
    go = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = ("check \"MonadPlus ParserBase\"", map (fmap (withMaxSuccess 1000000)) (snd (go undefined))) where
    go :: PB LocChr (Int, Int) -> TestBatch
    go = monadPlus

testParserBaseProperty :: IO ()
testParserBaseProperty = do
    quickBatch checkParserBaseIsMonad
    quickBatch checkParserBaseIsMonadPlus
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
