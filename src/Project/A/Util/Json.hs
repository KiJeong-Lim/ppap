module Project.A.Util.Json
    ( Json
    , object
    , array
    , field
    , string
    , int
    , bool
    , nullable
    , list
    ) where

type Json = String

object :: [(String, Json)] -> Json
object fields =
    "{\n" ++ indentBlock (commaLines [quote key ++ ": " ++ value | (key, value) <- fields]) ++ "\n}"

array :: [Json] -> Json
array values =
    "[" ++ commaInline values ++ "]"

field :: String -> Json -> (String, Json)
field = (,)

string :: String -> Json
string = quote

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

quote :: String -> String
quote str =
    "\"" ++ concatMap escape str ++ "\""

escape :: Char -> String
escape ch =
    case ch of
        '\"' -> "\\\""
        '\\' -> "\\\\"
        '\n' -> "\\n"
        '\r' -> "\\r"
        '\t' -> "\\t"
        c
            | c < ' ' -> "\\u" ++ pad4 (showHex4 (fromEnum c))
            | otherwise -> [c]

showHex4 :: Int -> String
showHex4 n =
    let digits = "0123456789abcdef"
        a = digits !! ((n `div` 4096) `mod` 16)
        b = digits !! ((n `div` 256) `mod` 16)
        c = digits !! ((n `div` 16) `mod` 16)
        d = digits !! (n `mod` 16)
     in [a, b, c, d]

pad4 :: String -> String
pad4 str = replicate (max 0 (4 - length str)) '0' ++ str

commaInline :: [String] -> String
commaInline [] = ""
commaInline [x] = x
commaInline (x : xs) = x ++ concatMap (", " ++) xs

commaLines :: [String] -> String
commaLines [] = ""
commaLines [x] = x
commaLines (x : xs) = x ++ concatMap (",\n" ++) xs

indentBlock :: String -> String
indentBlock =
    unlines . map ("  " ++) . lines
