module Project.A.Util.Json where

import Z.Utils

type Json = String

object :: [(String, Json)] -> Json
object = withZero . showObject

array :: [Json] -> Json
array = withZero . showArray

field :: String -> Json -> (String, Json)
field = (,)

string :: String -> Json
string = withZero . showStringLit

int :: Int -> Json
int = show

bool :: Bool -> Json
bool True = "true"
bool False = "false"

nullable :: (a -> Json) -> Maybe a -> Json
nullable _ Nothing = "null"
nullable f (Just x) = f x

list :: (a -> Json) -> [a] -> Json
list f = array . map f

showObject :: [(String, Json)] -> ShowS
showObject fields = strstr "{" . nl . pindent 2 . ppunc (withZero (strstr "," . nl . pindent 2)) [showStringLit key . strstr ": " . strstr value | (key, value) <- fields] . nl . strstr "}"

showArray :: [Json] -> ShowS
showArray values = strstr "[" . ppunc ", " (map strstr values) . strstr "]"

showStringLit :: String -> ShowS
showStringLit str = strstr "\"" . strcat (map showEscapedChar str) . strstr "\""

showEscapedChar :: Char -> ShowS
showEscapedChar '\"' = strstr "\\\""
showEscapedChar '\\' = strstr "\\\\"
showEscapedChar '\n' = strstr "\\n"
showEscapedChar '\r' = strstr "\\r"
showEscapedChar '\t' = strstr "\\t"
showEscapedChar ch = if ch < ' ' then strstr "\\u" . strstr (showHex4 (fromEnum ch)) else strstr [ch]

showHex4 :: Int -> String
showHex4 n = [digit 4096, digit 256, digit 16, digit 1] where
    digit :: Int -> Char
    digit k = "0123456789abcdef" !! ((n `div` k) `mod` 16)
