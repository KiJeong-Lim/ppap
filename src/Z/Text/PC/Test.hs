module Z.Text.PC.Test where

import Control.Applicative
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Algo.Function
import Z.Text.PC
import Z.Text.PC.Base
import Z.Text.PC.Internal
import Z.Utils

instance (Arbitrary chr, CoArbitrary chr, Arbitrary val) => Arbitrary (ParserBase chr val) where
    arbitrary = choose (0, 10) >>= recNat myInit myStep where
        myInit :: (Arbitrary val) => Gen (ParserBase chr val)
        myInit = frequency
            [ (10, PVal <$> arbitrary)
            ]
        myStep :: (Arbitrary chr, CoArbitrary chr, Arbitrary val) => Int -> Gen (ParserBase chr val) -> Gen (ParserBase chr val)
        myStep n prev = frequency
            [ (8, prev)
            , (2, PAct <$> (pure parsing <*> listOf prev <*> listOf arbitrary))
            ]
        parsing :: [p] -> [chr -> Bool] -> ([chr] -> [(p, [chr])])
        parsing ps (cond : conds) (ch : str) = if cond ch then parsing ps conds str else []
        parsing ps conds str = if null conds then [ (p, str) | p <- ps ] else []
    shrink = const []

instance Show (ParserBase chr val) where
    showsPrec prec = const id

instance (Show chr, Arbitrary chr, EqProp val, EqProp chr) => EqProp (ParserBase chr val) where
    p1 =-= p2 = execPB p1 =-= execPB p2

with100000 :: String -> TestBatch -> TestBatch
with100000 = curry (fmap (fmap (fmap (fmap (withMaxSuccess 100000))) snd))

checkParserBaseIsMonad :: TestBatch
checkParserBaseIsMonad = with100000 ">>> checking=\"Monad (ParserBase LocChr)\"" (checkMonad undefined) where
    checkMonad :: PB LocChr (Int, Int, Int) -> TestBatch
    checkMonad = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = with100000 ">>> checking=\"MonadPlus (ParserBase LocChr)\"" (checkMonadPlus undefined) where
    checkMonadPlus :: PB LocChr (Int, Int) -> TestBatch
    checkMonadPlus = monadPlus

testParserBaseProperty :: IO ()
testParserBaseProperty = do
    quickBatch checkParserBaseIsMonad
    quickBatch checkParserBaseIsMonadPlus
    return ()

testPC :: Int -> IO ()
testPC n = putStrLn (either id show (zipWith (runPC "Z\\Text\\PC\\Test.hs") getTestPC getTestInput !! n)) where
    getTestPC :: [PC String]
    getTestPC =
        [ pure (++) <*> regexPC "\"abc\"" <*> regexPC "\"defg \""
        , regexPC "\"abcdefg \""
        , regexPC "['0'-'9']*" <* skipWhite
        , regexPC "(['0'-'9']* \" \"*)*"
        , acceptQuote
        , acceptQuote
        , acceptQuote
        , acceptQuote
        , acceptQuote
        ]
    getTestInput :: [String]
    getTestInput =
        [ "abcdefg"
        , "abcdefg  "
        , "01234      "
        , "01 2  3   4"
        , "acceptQuote"
        , "ppap"
        , "\"hello\"\\\""
        , "\"'\""
        , "\"\\'\""
        ]
