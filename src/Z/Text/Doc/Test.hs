module Z.Text.Doc.Test where

import Data.IORef
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Text.Doc
import Z.Text.Doc.Internal

instance Arbitrary Doc_ where
    arbitrary = chooseInt (0, 10) >>= go where
        frequencyWith :: [Int] -> [Gen a] -> Gen a
        frequencyWith = curry (frequency . uncurry zip)
        chars :: Gen Char
        chars = elements ['a' .. 'z']
        strings :: Gen String
        strings = chooseInt (0, 100) >>= flip vectorOf (frequencyWith [90, 8, 2] [chars, pure '\n', pure '\t'])
        go :: Int -> Gen Doc
        go rank
            | rank > 0
            = frequencyWith [6, 2, 2]
                [ go (rank - 1)
                , pure DocVCat <*> go (rank - 1) <*> go (rank - 1)
                , pure DocHCat <*> go (rank - 1) <*> go (rank - 1)
                ]
            | otherwise
            = frequencyWith [8, 30, 10, 2]
                [ pure DocNull
                , pure DocText <*> strings
                , pure DocNemo <*> (chooseInt (0, 5) >>= flip vectorOf strings)
                , pure DocBeam <*> chars
                ]
    shrink = tail . getSubDocs where
        getSubDocs :: Doc -> [Doc]
        getSubDocs (DocNull) = [DocNull]
        getSubDocs (DocText str) = [DocText str]
        getSubDocs (DocHCat doc1 doc2) = [DocHCat doc1 doc2] ++ getSubDocs doc1 ++ getSubDocs doc2
        getSubDocs (DocVCat doc1 doc2) = [DocVCat doc1 doc2] ++ getSubDocs doc1 ++ getSubDocs doc2
        getSubDocs (DocNemo strs) = [DocNemo strs]

instance EqProp Doc_ where
    doc1 =-= doc2 = show doc1 =-= show doc2

testDoc :: IO ()
testDoc = go 8 where
    doc :: Int -> Doc
    doc 1 = vcat
        [ beam '-'
        , mconcat
            [ beam '|'
            , pstr " "
            , plist'
                [ pstr "Point" +> pnl +> pparen True "\t{ " "\n\t}" (ppunc (pnl +> pstr "\t, ") [pstr "x = " +> pprint 1, pstr "y = " +> pprint 2])
                , pstr "Point " +> pparen True "{ " " }" (ppunc (pstr ", ") [pstr "x = " +> pprint 3, pstr "y = " +> pprint 4])
                ]
            ]
        , beam '^'
        ]
    doc 2 = vcat []
    doc 3 = mconcat []
    doc 4 = pcat []
    doc 5 = vcat
        [ beam '-'
        , pstr " "
        , beam '-'
        ]
    doc 6 = vcat
        [ pstr ""
        , vcat
            [ pstr ""
            , pstr ""
            ]
        ]
    doc 7 = vcat
        [ vcat
            [ pstr ""
            , pstr ""
            ]
        , pstr ""
        ]
    doc 8 = vcat
        [ beam '-'
        , mconcat
            [ beam '|'
            , pstr " "
            , plist'
                [ pstr "Point" +> pnl +> ptab +> pblock (pparen True "{ " "\n}" (ppunc (pnl +> pstr ", ") [pstr "x = " +> pprint 1, pstr "y = " +> pprint 2]))
                , pstr "Point " +> pparen True "{ " " }" (ppunc (pstr ", ") [pstr "x = " +> pprint 3, pstr "y = " +> pprint 4])
                , pstr "Point" +> pnl +> ptab +> pblock (pparen True "{ " "\n}" (ppunc (pnl +> pstr ", ") [pstr "x = " +> pprint 5, pstr "y = " +> pprint 6]))
                ]
            ]
        , beam '^'
        ]
    str :: Int -> String
    str 1 = concat
        [ "--------------------------\n"
        , "| [ Point\n"
        , "|     { x = 1\n"
        , "|     , y = 2\n"
        , "|     }\n"
        , "| , Point { x = 3, y = 4 }\n"
        , "| ]\n"
        , "^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
        ]
    str 2 = ""
    str 3 = ""
    str 4 = ""
    str 5 = concat
        [ "-\n"
        , " \n"
        , "-\n"
        ]
    str 6 = "\n\n\n"
    str 7 = "\n\n\n"
    str 8 = concat
        [ "--------------------------\n"
        , "| [ Point\n"
        , "|     { x = 1\n"
        , "|     , y = 2\n"
        , "|     }\n"
        , "| , Point { x = 3, y = 4 }\n"
        , "| , Point\n"
        , "|     { x = 5\n"
        , "|     , y = 6\n"
        , "|     }\n"
        , "| ]\n"
        , "^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
        ]
    go :: Int -> IO ()
    go ea = do
        faileds_ref <- newIORef []
        sequence
            [ do
                let expected = str i
                    actual = show (doc i)
                if expected == actual
                    then return ()
                    else modifyIORef faileds_ref (\faileds -> faileds ++ [i])
            | i <- [1 .. ea]
            ]
        faileds <- readIORef faileds_ref
        if null faileds
            then putStrLn ("TEST.testZ.testDoc> " ++ "Print (all-cases-passed.).")
            else putStrLn ("TEST.testZ.testDoc> " ++ "Print ({" ++ shows (length faileds) ("}-cases-failed={\n  " ++ showList faileds "\n}.)."))

testDocIsMonoid :: IO ()
testDocIsMonoid = quickBatch (monoid doc) where
    doc :: Doc
    doc = undefined
