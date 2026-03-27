module Z.Doc where

import System.Console.Pretty
import Z.Algorithms
import Z.Utils

data Doc
    = DT !Int !Int [List (Char, (Maybe Style, Maybe Color))]
    | DB !Char (Maybe Style, Maybe Color)
    | DV !Doc !Doc
    | DH !Doc !Doc
    deriving ()

mkDT :: List [(Char, (Maybe Style, Maybe Color))] -> Doc
mkDT ss = DT (foldr (\s -> \acc -> length s `max` acc) 0 ss) (length ss) ss

text :: String -> Doc
text "" = mempty
text ss = mkDT [ map (\c -> (c, (Nothing, Nothing))) s | s <- lines ss ]

textit :: String -> Doc
textit "" = mempty
textit ss = mkDT [ map (\c -> (c, (Just Italic, Nothing))) s | s <- lines ss ]

textbf :: String -> Doc
textbf "" = mempty
textbf ss = mkDT [ map (\c -> (c, (Just Bold, Nothing))) s | s <- lines ss ]

red :: Doc -> Doc
red (DT row col ls) = DT row col [ map (uncurry $ \c -> uncurry $ \sty -> \clr -> (c, (sty, clr /> Just Red))) l | l <- ls ]
red (DB c (sty, clr)) = DB c (sty, clr /> Just Red)
red (DV d1 d2) = DV (red d1) (red d2)
red (DH d1 d2) = DH (red d1) (red d2)

blue :: Doc -> Doc
blue (DT row col ls) = DT row col [ map (uncurry $ \c -> uncurry $ \sty -> \clr -> (c, (sty, clr /> Just Blue))) l | l <- ls ]
blue (DB c (sty, clr)) = DB c (sty, clr /> Just Blue)
blue (DV d1 d2) = DV (blue d1) (blue d2)
blue (DH d1 d2) = DH (blue d1) (blue d2)

vcat :: [Doc] -> Doc
vcat [] = mkDT []
vcat [d] = d
vcat (d : ds) = DV d (vcat ds)

hcat :: [Doc] -> Doc
hcat [] = mempty
hcat [d] = d
hcat (d : ds) = d <> hcat ds

ptext :: Outputable a => a -> Doc
ptext = text . pshow

beam :: Char -> Doc
beam c = DB c (Just Bold, Nothing)

renderDoc :: Doc -> String
renderDoc = makeUp . mkBoard where
    mkBoard :: Doc -> [List (Char, (Maybe Style, Maybe Color))]
    mkBoard = unDT . normalizeV where
        getMaxHeight :: [Doc] -> Int
        getMaxHeight vs = foldr max 0 [ col | DT row col ls <- vs ]
        getMaxWidth :: [Doc] -> Int
        getMaxWidth vs = foldr max 0 [ row | DT row col ls <- vs ]
        expandHeight :: Int -> Doc -> Doc
        expandHeight col (DB c info) = DT 1 col (replicate col [(c, info)])
        expandHeight col (DT row col' field) = DT row col (field ++ replicate (col - col') (replicate row (' ', (Nothing, Nothing))))
        expandWidth :: Int -> Doc -> Doc
        expandWidth row (DB c info) = DT row 1 [replicate row (c, info)]
        expandWidth row (DT row' col field) = DT row col field
        horizontal :: Doc -> [Doc]
        horizontal (DB c info) = [DB c info]
        horizontal (DT row col field) = [DT row col field]
        horizontal (DH v1 v2) = horizontal v1 ++ horizontal v2
        horizontal v = [normalizeV v]
        vertical :: Doc -> [Doc]
        vertical (DB c info) = [DB c info]
        vertical (DT row col field) = [DT row col field]
        vertical (DV v1 v2) = vertical v1 ++ vertical v2
        vertical v = [normalizeH v]
        hsum :: Int -> [Doc] -> Doc
        hsum col [] = DT 0 col (replicate col [])
        hsum col (v : vs) = case (expandWidth' (expandHeight col v), hsum col vs) of
            (DT row1 _ field1, DT row2 _ field2) -> DT (row1 + row2) col (zipWith (++) field1 field2)
        vsum :: Int -> [Doc] -> Doc
        vsum row [] = DT row 0 []
        vsum row (v : vs) = case (expandWidth row v, vsum row vs) of
            (DT _ col1 field1, DT row' col2 field2) -> DT row (col1 + col2) (field1 ++ field2)
        expandWidth' :: Doc -> Doc
        expandWidth' (DT row col field) = DT row col [ if row == length str then str else str ++ replicate (row - length str) (' ', (Nothing, Nothing)) | str <- field ]
        normalizeH :: Doc -> Doc
        normalizeH = merge . concat . map horizontal . flatten where
            flatten :: Doc -> [Doc]
            flatten (DH v1 v2) = flatten v1 ++ flatten v2
            flatten v1 = [v1]
            merge :: [Doc] -> Doc
            merge vs = hsum (getMaxHeight vs) vs
        normalizeV :: Doc -> Doc
        normalizeV = merge . concat . map vertical . flatten where
            flatten :: Doc -> [Doc]
            flatten (DV v1 v2) = flatten v1 ++ flatten v2
            flatten v1 = [v1]
            merge :: [Doc] -> Doc
            merge vs = vsum (getMaxWidth vs) vs
        unDT :: Doc -> [List (Char, (Maybe Style, Maybe Color))]
        unDT (DT row col field) = field
    makeUp :: List [(Char, (Maybe Style, Maybe Color))] -> String
    makeUp = unlines . map (apply . group2 . group1) where
        group1 :: List (Char, (Maybe Style, Maybe Color)) -> List ((List Char, Maybe Style), Maybe Color)
        group1 [] = []
        group1 ((ch, (sty, clr)) : its) = ((ch : map fst (takeWhile cond its), sty), clr) : group1 (dropWhile cond its) where
            cond :: (Char, (Maybe Style, Maybe Color)) -> Bool
            cond (_, (sty', clr')) = sty == sty' && clr == clr'
        group2 :: List ((List Char, Maybe Style), Maybe Color) -> List (List (List Char, Maybe Style), Maybe Color)
        group2 [] = []
        group2 ((it, clr) : its) = (it : map fst (takeWhile cond its), clr) : group2 (dropWhile cond its) where
            cond :: ((List Char, Maybe Style), Maybe Color) -> Bool
            cond (_, clr') = clr == clr'
        apply :: List (List (List Char, Maybe Style), Maybe Color) -> String
        apply itss = do
            (its, clr) <- itss
            case clr of
                Nothing -> do
                    (it, sty) <- its
                    case sty of
                        Nothing -> it
                        Just sty -> style sty it
                Just clr -> do
                    (it, sty) <- its
                    case sty of
                        Nothing -> color clr it
                        Just sty -> color clr $ style sty it

instance Semigroup Doc where
    d1 <> d2 = DH d1 d2

instance Monoid Doc where
    mempty = DT 0 1 [[]]

instance Eq Color where
    Black   == Black   = True 
    Red     == Red     = True 
    Green   == Green   = True
    Yellow  == Yellow  = True
    Blue    == Blue    = True
    Magenta == Magenta = True
    Cyan    == Cyan    = True
    White   == White   = True
    Default == Default = True
    _       == _       = False

instance Eq Style where
    Normal        == Normal        = True
    Bold          == Bold          = True
    Faint         == Faint         = True
    Italic        == Italic        = True
    Underline     == Underline     = True
    SlowBlink     == SlowBlink     = True
    ColoredNormal == ColoredNormal = True
    Reverse       == Reverse       = True
    _             == _             = False
