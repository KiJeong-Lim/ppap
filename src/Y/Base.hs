module Y.Base where

import Z.Utils

type Indentation = Int

class Outputable a where
    pprint :: Precedence -> a -> String -> String

strstr :: String -> ShowS
strstr str1 str2 = str1 ++ str2

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id

nl :: ShowS
nl str = "\n" ++ str

pindent :: Indentation -> ShowS
pindent space str1 = if space < 0 then str1 else replicate space ' ' ++ str1

ppunc :: String -> [ShowS] -> ShowS
ppunc str [] = id
ppunc str (delta1 : deltas2) = delta1 . foldr (\delta2 -> \acc -> strstr str . delta2 . acc) id deltas2

plist :: Indentation -> [ShowS] -> ShowS
plist space [] = strstr "[]"
plist space (delta : deltas) = nl . pindent space . strstr "[ " . loop delta deltas where
    loop :: (ShowS) -> [ShowS] -> ShowS
    loop delta1 [] = delta1 . nl . pindent space . strstr "]"
    loop delta1 (delta2 : deltas) = delta1 . nl . pindent space . strstr ", " . loop delta2 deltas
