module Y.Base where

import Z.Utils

type Indentation = Int

class Outputable a where
    pprint :: Precedence -> a -> ShowS

instance Outputable Integer where
    pprint prec = if prec == 0 then byDigitsOf 3 else shows where
        byDigitsOf :: Int -> Integer -> ShowS
        byDigitsOf k n
            | n < 0 = strstr "- " . byDigitsOf k (negate n)
            | otherwise = if n >= (10 ^ k) then byDigitsOf k (n `div` (10 ^ k)) . strstr " " . strcat [ shows ((n `div` (10 ^ i)) `mod` 10) | i <- [k - 1, k - 2 .. 0] ] else shows n

strstr :: String -> ShowS
strstr = showString

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id

nl :: ShowS
nl = showString "\n"

pindent :: Indentation -> ShowS
pindent space = if space < 0 then id else showString (replicate space ' ')

ppunc :: String -> [ShowS] -> ShowS
ppunc str deltas = if null deltas then id else head deltas . foldr (\delta -> \acc -> strstr str . delta . acc) id (tail deltas)

plist' :: Indentation -> [ShowS] -> ShowS
plist' space deltas = nl . pindent space . strstr "[ " . ppunc (withZero (nl . pindent space . strstr ", ")) deltas . nl . pindent space . strstr "]"

plist :: Indentation -> [ShowS] -> ShowS
plist space deltas = if null deltas then strstr "[]" else plist' space deltas

quotify :: ShowS -> ShowS
quotify = shows . withZero

plist1 :: Indentation -> [ShowS] -> ShowS
plist1 space [] = strstr "[]"
plist1 space [delta] = strstr "[" . delta . strstr "]"
plist1 space deltas = plist' space deltas
