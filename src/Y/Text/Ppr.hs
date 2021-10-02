module Y.Text.Ppr where

import System.Console.Pretty
import Y.Base
import Y.Text.Ppr.Viewer
import qualified Z.Text.Doc.Internal as Z
import Z.Utils

data Doc
    = DE
    | DT String
    | DS Style Doc
    | DC Color Doc
    | DB
    | DV Doc Doc
    | DH Doc Doc
    deriving ()

instance Semigroup Doc where
    doc1 <> DE = doc1
    DE <> doc1 = doc1
    DH doc1 doc2 <> doc3 = happend doc1 (doc2 <> doc3)
    doc1 <> doc2 = happend doc1 doc2

instance Monoid Doc where
    mempty = empty
    
instance Show Doc where
    show = flip (showsPrec 0) ""
    showList [] str = "[]" ++ str
    showList (x : xs) str = "[" ++ go x xs str where
        go :: Doc -> [Doc] -> String -> String
        go doc1 [] str = showsPrec 0 doc1 ("]" ++ str)
        go doc1 (doc2 : docs) str = showsPrec 0 doc1 (", " ++ go doc2 docs str)
    showsPrec 0 doc1 str = showsPrec 1 doc1 str
    showsPrec 1 doc1 str = showsPrec 2 doc1 str
    showsPrec 2 doc1 str = showsPrec 3 doc1 str
    showsPrec 3 doc1 str = showsPrec 4 doc1 str
    showsPrec 4 doc1 str = showsPrec 5 doc1 str
    showsPrec 5 doc1 str = showsPrec 6 doc1 str
    showsPrec 6 doc1 str = showsPrec 7 doc1 str
    showsPrec 7 doc1 str = showsPrec 8 doc1 str
    showsPrec 8 doc1 str = showsPrec 9 doc1 str
    showsPrec 9 (DT str1) str = "DT " ++ showsPrec 0 str1 str
    showsPrec 9 (DS style1 doc1) str = "DS " ++ showStyle style1 (" " ++ showsPrec 10 doc1 str) where
        showStyle :: Style -> String -> String
        showStyle Normal str = "Normal" ++ str
        showStyle Bold str = "Bold" ++ str
        showStyle Faint str = "Faint" ++ str
        showStyle Italic str = "Italic" ++ str
        showStyle Underline str = "Underline" ++ str
        showStyle SlowBlink str = "SlowBlink" ++ str
        showStyle ColoredNormal str = "ColoredNormal" ++ str
        showStyle Reverse str = "Reverse" ++ str
    showsPrec 9 (DC color1 doc1) str = "DC " ++ showColor color1 (" " ++ showsPrec 10 doc1 str) where
        showColor :: Color -> String -> String
        showColor Black str = "Black" ++ str
        showColor Red str = "Red" ++ str
        showColor Green str = "Green" ++ str
        showColor Yellow str = "Yellow" ++ str
        showColor Blue str = "Blue" ++ str
        showColor Magenta str = "Magenta" ++ str
        showColor Cyan str = "Cyan" ++ str
        showColor White str = "White" ++ str
        showColor Default str = "Default" ++ str
    showsPrec 9 (DV doc1 doc2) str = "DV " ++ showsPrec 10 doc1 (" " ++ showsPrec 10 doc2 str)
    showsPrec 9 (DH doc1 doc2) str = "DH " ++ showsPrec 10 doc1 (" " ++ showsPrec 10 doc2 str)
    showsPrec 10 DE str = "DE" ++ str
    showsPrec 10 DB str = "DB" ++ str
    showsPrec _ doc1 str = "(" ++ showsPrec 0 doc1 (")" ++ str)

instance Outputable Char where
    pprint _ = strstr . Z.dispatchChar

empty :: Doc
empty = DE

happend :: Doc -> Doc -> Doc
happend doc1 doc2 = doc1 `seq` doc2 `seq` DH doc1 doc2

vappend :: Doc -> Doc -> Doc
vappend doc1 doc2 = doc1 `seq` doc2 `seq` DV doc1 doc2

text :: String -> Doc
text = DT

textit :: String -> Doc
textit str = DS Italic (text str)

textbf :: String -> Doc
textbf str = DS Bold (text str)

hconcat :: [Doc] -> Doc
hconcat = foldr happend empty

vconcat :: [Doc] -> Doc
vconcat = foldr vappend empty

mkBeam :: Doc
mkBeam = DB

white :: Int -> Doc
white = text . flip replicate ' '

blue :: Doc -> Doc
blue = DC Blue

red :: Doc -> Doc
red = DC Red

indent :: Int -> [Doc] -> Doc
indent n docs1 = if null docs1 then empty else white n <> vconcat docs1

putDoc :: Show a => Precedence -> a -> Doc
putDoc prec = DT . flip (showsPrec prec) ""

renderDoc :: Doc -> String
renderDoc = render . toViewer . reduce where
    reduce :: Doc -> Doc
    reduce (DE) = DE
    reduce (DT str1) = DT str1
    reduce (DS style1 doc1) = DS style1 (reduce doc1)
    reduce (DC color1 doc1) = DC color1 (reduce doc1)
    reduce (DB) = DB
    reduce (DV doc1 doc2) = DV (reduce doc1) (reduce doc2)
    reduce (DH doc1 doc2) = case (reduce doc1, reduce doc2) of
        (DE, doc2') -> doc2'
        (doc1', DE) -> doc1'
        (DT str1, DT str2) -> DT (str1 ++ str2)
        (doc1', doc2') -> DH doc1' doc2'
    toViewer :: Doc -> Viewer
    toViewer (DE) = mkVE
    toViewer (DT str1) = mkVT str1
    toViewer (DS style1 doc1) = mkVS style1 (toViewer doc1)
    toViewer (DC color1 doc1) = mkVC color1 (toViewer doc1)
    toViewer (DB) = mkVB
    toViewer (DV doc1 doc2) = mkVV (toViewer doc1) (toViewer doc2)
    toViewer (DH doc1 doc2) = mkVH (toViewer doc1) (toViewer doc2)

pprintChar :: Char -> String -> String
pprintChar ch = strstr "\\\'" . pprint 0 ch . strstr "\\\'"

pprintString :: String -> String -> String
pprintString str = strstr "\"" . strcat (map (pprint 0) str) . strstr "\""
