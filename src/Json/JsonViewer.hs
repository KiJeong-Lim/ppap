module Json.JsonViewer where

import Json.JsonAst
import Json.JsonLexer
import Json.JsonParser
import Y.Base

prettyjson :: ValueRep -> String
prettyjson js_input
    = case showsjson 0 js_input "" of
        '\n' : str -> str
        str -> str
    where
        tabjson :: Indentation -> Indentation
        tabjson space = space + 4
        showsjsnum :: NumberRep -> ShowS
        showsjsnum (NumberRep_integer n) = strstr n
        showsjsnum (NumberRep_fraction q) = strstr q
        showsjsnum (NumberRep_exponent x) = strstr x
        showsobject :: Indentation -> ObjectRep -> ShowS
        showsobject space [] = strstr "{}"
        showsobject space ((field1, val1) : elements) = strcat
            [ nl . pindent space . strstr "{ " . strstr field1 . strstr " : " . showsjson (tabjson space) val1
            , strcat $ map (uncurry $ \field -> \val -> nl . pindent space . strstr ", " . strstr field . strstr " : " . showsjson (tabjson space) val) elements
            , nl . pindent space . strstr "}"
            ]
        showsjson :: Indentation -> ValueRep -> ShowS
        showsjson space (ValueRep_object obj) = showsobject space obj
        showsjson space (ValueRep_array ary) = plist space (map (showsjson (tabjson space)) ary)
        showsjson space (ValueRep_string str) = strstr str
        showsjson space (ValueRep_number num) = showsjsnum num
        showsjson space (ValueRep_true) = strstr "true"
        showsjson space (ValueRep_false) = strstr "false"
        showsjson space (ValueRep_null) = strstr "null"
