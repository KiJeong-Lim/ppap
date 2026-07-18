module Json.JsonViewer (prettyjson) where

import Json.JsonAst
import Json.JsonLexer
import Json.JsonParser
import Y.Base

type Precedence = Int

prettyjson :: ValueRep -> String
prettyjson js_input = showsjson 0 0 js_input "" where
    tabjson :: Indentation -> Indentation
    tabjson space = space + 2
    showsjsnum :: NumberRep -> ShowS
    showsjsnum (NumberRep_integer n) = strstr n
    showsjsnum (NumberRep_fraction q) = strstr q
    showsjsnum (NumberRep_exponent x) = strstr x
    showsobject :: Precedence -> Indentation -> ObjectRep -> ShowS
    showsobject prec space [] = strstr "{}"
    showsobject prec space ((field1, val1) : elements) = strcat
        [ (if prec > 0 then nl . pindent space else id) . strstr "{ " . addField field1 . showsjson 1 (tabjson space) val1
        , strcat $ map (uncurry $ \field -> \val -> nl . pindent space . strstr ", " . addField field . showsjson 1 (tabjson space) val) elements
        , nl . pindent space . strstr "}"
        ]
    showsjson :: Precedence -> Indentation -> ValueRep -> ShowS
    showsjson prec space (ValueRep_object obj) = showsobject prec space obj
    showsjson prec space (ValueRep_array ary) = plist space (map (showsjson 0 (tabjson space)) ary)
    showsjson prec space (ValueRep_string str) = strstr str
    showsjson prec space (ValueRep_number num) = showsjsnum num
    showsjson prec space (ValueRep_true) = strstr "true"
    showsjson prec space (ValueRep_false) = strstr "false"
    showsjson prec space (ValueRep_null) = strstr "null"
    addField :: String -> ShowS
    addField field = strstr field . strstr ": "
