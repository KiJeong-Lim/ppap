module Z.Text.Doc where

import Z.Text.Doc.Viewer
import Z.Utils

infixr 9 +>

type Indentation = Int

class Outputable a where
    pretty :: Precedence -> a -> Doc

instance Outputable Char where
    pretty _ = go . dispatch where
        dispatch :: Char -> String
        dispatch '\n' = "\\n"
        dispatch '\t' = "\\t"
        dispatch '\\' = "\\\\"
        dispatch '\"' = "\\\""
        dispatch '\'' = "\\\'"
        dispatch ch = [ch]
        go :: String -> Doc
        go str = pstr ("\'" ++ str ++ "\'")

vcat :: [Doc] -> Doc
vcat = foldr DocVCat DocNull

hcat :: [Doc] -> Doc
hcat = foldr DocHCat DocNull

beam :: Doc
beam = DocBeam

pstr :: String -> Doc
pstr str = if null str then DocNull else DocText str

pprint :: Show a => a -> Doc
pprint = pstr . show

(+>) :: Doc -> Doc -> Doc
DocNull +> doc = doc
doc +> DocNull = doc
DocText str1 +> DocText str2 = DocText (str1 ++ str2)
doc1 +> doc2 = DocHCat doc1 doc2

pcat :: [Doc] -> Doc
pcat = foldr (+>) DocNull

ptab :: Doc
ptab = DocText "\t"

pnl :: Doc
pnl = DocText "\n"

ppunc :: String -> [Doc] -> Doc
ppunc str [] = DocNull
ppunc str (doc1 : docs2) = doc1 +> foldr (\delta2 -> \acc -> pstr str +> delta2 +> acc) DocNull docs2

pparen :: String -> String -> Doc -> Doc
pparen left right doc = pstr left +> doc +> pstr right

plist :: [Doc] -> Doc
plist [] = pstr "[]"
plist (doc : docs) = pnl +> ptab +> pstr "[ " +> go doc docs where
    go :: Doc -> [Doc] -> Doc
    go doc1 [] = doc1 +> pnl +> ptab +> pstr "]"
    go doc1 (doc2 : docs3) = doc1 +> pnl +> ptab +> pstr ", " +> go doc2 docs3

pquote :: String -> Doc
pquote str = pstr ("\""  ++ (str >>= dispatch) ++ "\"") where
    dispatch :: Char -> String
    dispatch '\n' = "\\n"
    dispatch '\t' = "\\t"
    dispatch '\\' = "\\\\"
    dispatch '\"' = "\\\""
    dispatch '\'' = "\\\'"
    dispatch ch = [ch]
