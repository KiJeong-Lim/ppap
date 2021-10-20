module Y.Base where

import Z.Utils

type Indentation = Int

class Outputable a where
    pprint :: Precedence -> a -> ShowS

instance Outputable Integer where
    pprint prec = if prec == 0 then by3digits else shows where
        by3digits :: Integer -> ShowS
        by3digits n
            | n < 0 = strstr "- " . by3digits (abs n)
            | n >= 1000 = by3digits (n `div` 1000) . shows (n `mod` 1000)
            | otherwise = shows n

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

plist :: Indentation -> [ShowS] -> ShowS
plist space deltas = if null deltas then strstr "[]" else nl . pindent space . strstr "[ " . ppunc (runShowS (nl . pindent space . strstr ", ")) deltas . nl . pindent space . strstr "]" where
    runShowS :: ShowS -> String
    runShowS ss = ss ""

quotify :: ShowS -> ShowS
quotify ss = shows (ss "")
