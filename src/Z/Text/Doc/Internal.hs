module Z.Text.Doc.Internal where

import Text.Show

data Doc_
    = DocNull
    | DocText String
    | DocHCat Doc_ Doc_
    | DocVCat Doc_ Doc_
    | DocBeam Char
    | DocNemo [String]
    deriving ()

data Viewer
    = VE
    | VB Char
    | VV Viewer Viewer
    | VH Viewer Viewer
    | VF Int Int [String]
    deriving (Eq, Show)

instance Eq Doc_ where
    doc1 == doc2 = show doc1 == show doc2

instance Show Doc_ where
    showsPrec _ = showString . alliance . renderViewer . toViewer
    showList = showsPrec 0 . foldr DocVCat DocNull
    show = flip (showsPrec 0) ""

calcTab :: Int -> Int
calcTab n = tabsz - (n `mod` tabsz) where
    tabsz :: Int
    tabsz = 4

one :: a -> [a]
one x = x `seq` [x]

mkVE :: Viewer
mkVE = VE

mkVN :: [String] -> Viewer
mkVN strs = mkVF (foldr max 0 (map length strs)) (length strs) strs

mkVT :: String -> Viewer
mkVT = mkVN . makeBoard where
    makeBoard :: String -> [String]
    makeBoard = go "" where
        go :: String -> String -> [String]
        go buf [] = flush buf
        go buf (ch : str)
            | ch == '\n' = flush buf ++ go "" str
            | ch == '\t' = go (replicate (calcTab (length buf)) ' ' ++ buf) str
            | otherwise = go (ch : buf) str
        flush :: String -> [String]
        flush buf = one (reverse buf)

mkVB :: Char -> Viewer
mkVB = VB

mkVV :: Viewer -> Viewer -> Viewer
mkVV v1 v2 = v1 `seq` v2 `seq` VV v1 v2

mkVH :: Viewer -> Viewer -> Viewer
mkVH v1 v2 = v1 `seq` v2 `seq` VH v1 v2

mkVF :: Int -> Int -> [String] -> Viewer
mkVF row col field = row `seq` col `seq` VF row col field

toViewer :: Doc_ -> Viewer
toViewer (DocNull) = mkVE
toViewer (DocText str) = mkVT str
toViewer (DocHCat doc1 doc2) = mkVH (toViewer doc1) (toViewer doc2)
toViewer (DocVCat doc1 doc2) = mkVV (toViewer doc1) (toViewer doc2)
toViewer (DocBeam ch) = mkVB ch
toViewer (DocNemo strs) = mkVN strs

calcIndentation :: String -> Int
calcIndentation = flip go 0 where
    go :: String -> Int -> Int
    go [] res = res
    go (ch : str) res
        | ch == '\n' = go str 0
        | ch == '\t' = go str (res + calcTab res)
        | otherwise = go str (res + 1)

nemotext :: [String] -> String -> Doc_
nemotext strs1 str2 = DocNemo (go strs1) where
    go :: [String] -> [String]
    go [] = [str2]
    go [str] = [str ++ str2]
    go (str : strs) = str : go strs

textnemo :: String -> [String] -> Doc_
textnemo str1 = DocText . showString str1 . go where
    indent :: Int
    indent = calcIndentation str1
    go :: [String] -> String
    go [] = ""
    go [str] = str
    go (str : strs) = str ++ "\n" ++ replicate indent ' ' ++ go strs

nemonemo :: [String] -> [String] -> Doc_
nemonemo strs1 strs2 = nemotext strs1 (alliance strs2)

alliance :: [String] -> String
alliance [] = ""
alliance [str] = str
alliance strs = foldr (\str -> showString str . showChar '\n') "" strs

renderViewer :: Viewer -> [String]
renderViewer = intoStrings . normalizeV where
    getMaxHeight :: [Viewer] -> Int
    getMaxHeight vs = foldr max 0 [ col | VF row col field <- vs ]
    getMaxWidth :: [Viewer] -> Int
    getMaxWidth vs = foldr max 0 [ row | VF row col field <- vs ]
    expandHeight :: Int -> Viewer -> Viewer
    expandHeight col (VB ch) = mkVF 1 col (replicate col [ch])
    expandHeight col (VF row col' field) = mkVF row col (field ++ replicate (col - col') "")
    expandHeight col v = v
    expandWidth :: Int -> Viewer -> Viewer
    expandWidth row (VB ch) = mkVF row 1 [replicate row ch]
    expandWidth row (VE) = mkVF row 0 [""]
    expandWidth row v = v
    horizontal :: Viewer -> [Viewer]
    horizontal (VB ch) = one (mkVB ch)
    horizontal (VE) = one mkVE
    horizontal (VF row col field) = one (mkVF row col field)
    horizontal (VV v1 v2) = one (normalizeV (mkVV v1 v2))
    horizontal (VH v1 v2) = horizontal v1 ++ horizontal v2
    vertical :: Viewer -> [Viewer]
    vertical (VB ch) = one (mkVB ch)
    vertical (VE) = one mkVE
    vertical (VF row col field) = one (mkVF row col field)
    vertical (VV v1 v2) = vertical v1 ++ vertical v2
    vertical (VH v1 v2) = one (normalizeH (mkVH v1 v2))
    stretch :: Viewer -> Viewer
    stretch (VF row col strs) = mkVF row col [ str ++ replicate (row - length str) ' ' | str <- strs ]
    hsum :: Int -> [Viewer] -> Viewer
    hsum col [] = mkVF 0 col (replicate col "")
    hsum col [v] = v
    hsum col (v : vs) = case (stretch v, hsum col vs) of
        (VF row1 _ field1, VF row2 _ field2) -> mkVF (row1 + row2) col (zipWith (++) field1 field2)
    vsum :: Int -> [Viewer] -> Viewer
    vsum row [] = mkVF row 0 []
    vsum row (v : vs) = case (v, vsum row vs) of
        (VF _ col1 field1, VF _ col2 field2) -> mkVF row (col1 + col2) (field1 ++ field2)
    normalizeH :: Viewer -> Viewer
    normalizeH = merge . concat . map horizontal . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VH v1 v2) = flatten v1 ++ flatten v2
        flatten (VE) = []
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = hsum (getMaxHeight vs) (map (expandHeight (getMaxHeight vs)) vs)
    normalizeV :: Viewer -> Viewer
    normalizeV = merge . concat . map vertical . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VV v1 (VE)) = flatten v1
        flatten (VV v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = vsum (getMaxWidth vs) (map (expandWidth (getMaxWidth vs)) vs)
    intoStrings :: Viewer -> [String]
    intoStrings (VF row col field) = field
