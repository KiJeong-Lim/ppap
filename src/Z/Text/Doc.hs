module Z.Text.Doc where

import Z.Text.Doc.Internal
import Z.Utils

infixr 9 +>

type Doc = Doc_

class PrettyPrintable a where
    pretty :: Precedence -> a -> Doc

instance OStreamCargo Doc_ where
    hput h = hput h . shows

instance PrettyPrintable Char where
    pretty _ ch = pstr ("\'" ++ dispatchChar ch ++ "\'")

isEmptyDoc :: Doc -> Bool
isEmptyDoc (DocNull) = True
isEmptyDoc (DocText str) = null str
isEmptyDoc (DocHCat doc1 doc2) = isEmptyDoc doc1 && isEmptyDoc doc2
isEmptyDoc (DocVCat doc1 doc2) = False
isEmptyDoc (DocBeam ch) = False
isEmptyDoc (DocNemo strs) = null (alliance strs)

vcat :: [Doc] -> Doc
vcat = foldr DocVCat DocNull

beam :: Char -> Doc
beam = DocBeam

pstr :: String -> Doc
pstr str = if null str then DocNull else DocText str

pp :: Show a => a -> Doc
pp = pstr . withZero . shows

(+>) :: Doc -> Doc -> Doc
DocNull +> doc = doc
doc +> DocNull = doc
DocText str1 +> DocText str2 = pstr (str1 ++ str2)
DocText str1 +> DocNemo strs2 = textnemo str1 strs2
DocNemo strs1 +> DocText str2 = nemotext strs1 str2
DocNemo strs1 +> DocNemo strs2 = nemonemo strs1 strs2
doc1 +> doc2 = doc1 <> doc2

pcat :: [Doc] -> Doc
pcat = foldr (+>) DocNull

ptab :: Doc
ptab = DocText "\t"

pnl :: Doc
pnl = DocText "\n"

pblock :: Doc -> Doc
pblock = DocNemo . renderViewer . toViewer

ppunc' :: Doc -> [Doc] -> Doc
ppunc' doc0 [] = DocNull
ppunc' doc0 (doc1 : docs2) = doc1 +> foldr (\doc2 -> \acc -> doc0 +> doc2 +> acc) DocNull docs2

pparen :: Bool -> String -> String -> Doc -> Doc
pparen b left right doc = if b then pstr left +> doc +> pstr right else doc

plist' :: [Doc] -> Doc
plist' docs = pstr "[ " +> ppunc' (pstr "\n, ") docs +> pstr "\n]"

pquote :: String -> Doc
pquote str = pstr ("\"" ++ (str >>= dispatchChar) ++ "\"")

plist0 :: [Doc] -> Doc
plist0 docs = if null docs then pblock (plist' docs) else ptab +> pblock (plist' docs)
