module Z.Text.PM where

import Control.Applicative
import Control.Monad
import Z.Utils

newtype PM a
    = PM { unPM :: ReadS a }
    deriving ()

instance Functor PM where
    fmap a2b p1 = PM $ \str0 -> [ (a2b a, str1) | (a, str1) <- unPM p1 str0 ]

instance Applicative PM where
    pure a = PM $ \str0 -> [(a, str0)]
    p1 <*> p2 = PM $ \str0 -> [ (a2b a, str2) | (a2b, str1) <- unPM p1 str0, (a, str2) <- unPM p2 str1 ]

instance Monad PM where
    return = PM . curry pure
    p1 >>= p2 = PM (flip (>>=) (uncurry (unPM . p2)) . unPM p1)

instance Alternative PM where
    empty = PM (pure [])
    p1 <|> p2 = PM (pure (++) <*> unPM p1 <*> unPM p2)

instance MonadPlus PM where

instance MonadFail PM where
    fail = const empty

instance Semigroup (PM a) where
    p1 <> p2 = p1 <|> p2

instance Monoid (PM a) where
    mempty = empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM $ \str -> let ch = head str in if null str then [] else if condition ch then [(ch, tail str)] else []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []
