module Z.Text.Doc.Viewer where

import Data.Monoid
import Text.Show

data Doc
    = DocNull
    | DocText String
    | DocHCat Doc Doc
    | DocVCat Doc Doc
    | DocBeam
    deriving ()

data Viewer
    = VE
    | VT String
    | VB
    | VV Viewer Viewer
    | VH Viewer Viewer
    | VF Int Int [String]
    deriving (Eq, Show)

instance Eq Doc where
    DocNull == DocNull = True
    DocText str == DocText str' = str == str'
    DocHCat doc1 doc2 == DocHCat doc1' doc2' = doc1 == doc1' && doc2 == doc2'
    DocVCat doc1 doc2 == DocVCat doc1' doc2' = doc1 == doc1' && doc2 == doc2'
    DocBeam == DocBeam = True
    DocNull == DocText str = null str
    DocText str == DocNull = null str
    _ == _ = False

instance Show Doc where
    showsPrec _ = showString . renderViewer . toViewer
    showList = appEndo . mconcat . map (Endo . shows)
    show = flip shows ""

mkVE :: Viewer
mkVE = VE

mkVT :: String -> Viewer
mkVT str1 = str1 `seq` VT str1

mkVB :: Viewer
mkVB = VB

mkVV :: Viewer -> Viewer -> Viewer
mkVV v1 v2 = v1 `seq` v2 `seq` VV v1 v2

mkVH :: Viewer -> Viewer -> Viewer
mkVH v1 v2 = v1 `seq` v2 `seq` VH v1 v2

mkVF :: Int -> Int -> [String] -> Viewer
mkVF row col field = row `seq` col `seq` field `seq` VF row col field

one :: a -> [a]
one x = x `seq` [x]

toViewer :: Doc -> Viewer
toViewer (DocNull) = mkVE
toViewer (DocText str) = mkVT str
toViewer (DocHCat doc1 doc2) = mkVH (toViewer doc1) (toViewer doc2)
toViewer (DocVCat doc1 doc2) = mkVV (toViewer doc1) (toViewer doc2)
toViewer (DocBeam) = mkVB

trimLines :: String -> String
trimLines = go 0 where
    go :: Int -> String -> String
    go n [] = []
    go n (ch : str)
        | ch == ' ' = go (n + 1) str
        | otherwise = replicate n ' ' ++ ch : go 0 str

viewText :: String -> Viewer
viewText = mkVField . makeBoard where
    makeBoard :: String -> [String]
    makeBoard = go id where
        tabsz :: Int
        tabsz = 4
        go :: ShowS -> String -> [String]
        go buf [] = flush buf
        go buf (ch : str)
            | ch == '\n' = flush buf ++ makeBoard str
            | ch == '\t' = go (buf . showString (replicate tabsz ' ')) str
            | otherwise = go (buf . showChar ch) str
        flush :: ShowS -> [String]
        flush buf = [buf ""]
    mkVField :: [String] -> Viewer
    mkVField strs = mkVF row (length strs) [ str ++ replicate (row - length str) ' ' | str <- strs ] where
        row :: Int
        row = foldr max 0 (map length strs)

renderViewer :: Viewer -> String 
renderViewer = unlines . map trimLines . linesFromVField . normalizeV where
    getMaxHeight :: [Viewer] -> Int
    getMaxHeight vs = foldr max 0 [ col | VF row col field <- vs ]
    getMaxWidth :: [Viewer] -> Int
    getMaxWidth vs = foldr max 0 [ row | VF row col field <- vs ]
    expandHeight :: Int -> Viewer -> Viewer
    expandHeight col (VB) = mkVF 1 col (replicate col "|")
    expandHeight col (VE) = mkVF 0 col (replicate col "")
    expandHeight col (VF row col' field) = mkVF row col (field ++ replicate (col - col') (replicate row ' '))
    expandWidth :: Int -> Viewer -> Viewer
    expandWidth row (VB) = mkVF row 1 [replicate row '-']
    expandWidth row (VE) = mkVF row 0 []
    expandWidth row (VF row' col field) = mkVF row col [ str ++ replicate (row - row') ' ' | str <- field ]
    horizontal :: Viewer -> [Viewer]
    horizontal (VB) = one mkVB
    horizontal (VE) = one mkVE
    horizontal (VF row col field) = one (mkVF row col field)
    horizontal (VT str) = one (viewText str)
    horizontal (VV v1 v2) = one (normalizeV (mkVV v1 v2))
    horizontal (VH v1 v2) = horizontal v1 ++ horizontal v2
    vertical :: Viewer -> [Viewer]
    vertical (VB) = one mkVB
    vertical (VE) = one mkVE
    vertical (VF row col field) = one (mkVF row col field)
    vertical (VT str) = one (viewText str)
    vertical (VV v1 v2) = vertical v1 ++ vertical v2
    vertical (VH v1 v2) = one (normalizeV (mkVH v1 v2))
    hsum :: Int -> [Viewer] -> Viewer
    hsum col [] = mkVF 0 col (replicate col "")
    hsum col (v : vs) = case (v, hsum col vs) of
        (VF row1 _ field1, VF row2 _ field2) -> mkVF (row1 + row2) col (zipWith (++) field1 field2)
    vsum :: Int -> [Viewer] -> Viewer
    vsum row [] = mkVF row 0 []
    vsum row (v : vs) = case (v, vsum row vs) of
        (VF _ col1 field1, VF _ col2 field2) -> mkVF row (col1 + col2) (field1 ++ field2)
    normalizeH :: Viewer -> Viewer
    normalizeH = merge . concat . map horizontal . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VH v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = hsum (getMaxHeight vs) (map (expandHeight (getMaxHeight vs)) vs)
    normalizeV :: Viewer -> Viewer
    normalizeV = merge . concat . map vertical . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VV v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = vsum (getMaxWidth vs) (map (expandWidth (getMaxWidth vs)) vs)
    linesFromVField :: Viewer -> [String]
    linesFromVField (VF row col field) = field
