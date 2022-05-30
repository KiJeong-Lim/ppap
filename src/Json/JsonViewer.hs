module Json.JsonViewer where

import Json.JsonAst
import Json.JsonLexer
import Json.JsonParser
import Y.Base

showjson :: Value -> String
showjson js_input = showsjson 0 js_input ""

showsjsnum :: Number -> ShowS
showsjsnum (Number_integer n) = shows n
showsjsnum (Number_fraction q) = shows q
showsjsnum (Number_exponent x) = shows x

tabjson :: Indentation -> Indentation
tabjson space = space + 4

showsobject :: Indentation -> Object -> ShowS
showsobject space [] = strstr "{}"
showsobject space ((field1, val1) : elements) = strcat
    [ nl . pindent space . strstr "{ " . shows field1 . strstr " : " . showsjson (tabjson space) val1
    , strcat $ map (uncurry $ \field -> \val -> nl . pindent space . strstr ", " . shows field . strstr " : " . showsjson (tabjson space) val) elements
    , nl . pindent space . strstr "}"
    ]

showsjson :: Indentation -> Value -> ShowS
showsjson space (Value_object obj) = showsobject space obj
showsjson space (Value_array ary) = plist space (map (showsjson (tabjson space)) ary)
showsjson space (Value_string str) = shows str
showsjson space (Value_number num) = showsjsnum num
showsjson space (Value_true) = strstr "true"
showsjson space (Value_false) = strstr "false"
showsjson space (Value_null) = strstr "null"
