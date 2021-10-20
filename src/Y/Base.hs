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
ppunc str deltas
    | null deltas = id
    | otherwise = head deltas . foldr (\delta -> \acc -> strstr str . delta . acc) id (tail deltas)

plist :: Indentation -> [ShowS] -> ShowS
plist space deltas = if null deltas then strstr "[]" else nl . pindent space . strstr "[ " . ppunc ("\n" ++ replicate space ' ' ++ ", ") deltas . nl . pindent space . strstr "]"

quotify :: ShowS -> ShowS
quotify ss = shows (ss "")
