module Y.Base where

import Z.Utils

type Indentation = Int

class Outputable a where
    pprint :: Precedence -> a -> String -> String

strstr :: String -> String -> String
strstr str1 str2 = str1 ++ str2

strcat :: [String -> String] -> String -> String
strcat = foldr (.) id

nl :: String -> String
nl str = "\n" ++ str

pindent :: Indentation -> String -> String
pindent space str1 = if space < 0 then str1 else replicate space ' ' ++ str1

ppunc :: String -> [String -> String] -> String -> String
ppunc str [] = id
ppunc str (delta1 : deltas2) = delta1 . foldr (\delta2 -> \acc -> strstr str . delta2 . acc) id deltas2

plist :: Indentation -> [String -> String] -> String -> String
plist space [] = strstr "[]"
plist space (delta : deltas) = nl . pindent space . strstr "[ " . loop delta deltas where
    loop :: (String -> String) -> [String -> String] -> String -> String
    loop delta1 [] = delta1 . nl . pindent space . strstr "]"
    loop delta1 (delta2 : deltas) = delta1 . nl . pindent space . strstr ", " . loop delta2 deltas

printPretty :: Outputable a => a -> String
printPretty = flip (pprint 0) ""
