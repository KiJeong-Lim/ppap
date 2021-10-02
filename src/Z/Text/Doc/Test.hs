module Z.Text.Doc.Test where

import Data.IORef
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.System.Shelly
import Z.Text.Doc
import Z.Text.Doc.Internal
import Z.Utils

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

docshunt :: Int -> Doc
docshunt 1 = vcat
    [ beam '-'
    , mconcat
        [ beam '|'
        , pstr " "
        , plist'
            [ pstr "Point" +> pnl +> pparen True "\t{ " "\n\t}" (ppunc' (pnl +> pstr "\t, ") [pstr "x = " +> pp 1, pstr "y = " +> pp 2])
            , pstr "Point " +> pparen True "{ " " }" (ppunc' (pstr ", ") [pstr "x = " +> pp 3, pstr "y = " +> pp 4])
            ]
        ]
    , beam '^'
    ]
docshunt 2 = vcat []
docshunt 3 = mconcat []
docshunt 4 = pcat []
docshunt 5 = vcat
    [ beam '-'
    , pstr " "
    , beam '-'
    ]
docshunt 6 = vcat
    [ pstr ""
    , vcat
        [ pstr ""
        , pstr ""
        ]
    ]
docshunt 7 = vcat
    [ vcat
        [ pstr ""
        , pstr ""
        ]
    , pstr ""
    ]
docshunt 8 = vcat
    [ beam '-'
    , mconcat
        [ beam '|'
        , pstr " "
        , plist'
            [ pstr "Point" +> pnl +> ptab +> pblock (pparen True "{ " "\n}" (ppunc' (pnl +> pstr ", ") [pstr "x = " +> pp 1, pstr "y = " +> pp 2]))
            , pstr "Point " +> pparen True "{ " " }" (ppunc' (pstr ", ") [pstr "x = " +> pp 3, pstr "y = " +> pp 4])
            , pstr "Point" +> pnl +> ptab +> pblock (pparen True "{ " "\n}" (ppunc' (pnl +> pstr ", ") [pstr "x = " +> pp 5, pstr "y = " +> pp 6]))
            ]
        ]
    , beam '^'
    ]
docshunt 9 = vcat
    [ pstr "main :: IO ()"
    , pstr "main = " +> pparen True "do\n\t" "" (pblock (ppunc' pnl [pstr "putStrLn " +> pquote "Hello, world!", pstr "return ()"]))
    , pstr ""
    , pstr "x :: Int"
    , pstr "x = 3"
    ]

testDoc :: IO ()
testDoc = go 9 where
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
    str 9 = concat
        [ "main :: IO ()\n"
        , "main = do\n"
        , "    putStrLn \"Hello, world!\"\n"
        , "    return ()\n"
        , "\n"
        , "x :: Int\n"
        , "x = 3\n"
        ]
    go :: Int -> IO ()
    go ea = do
        faileds_ref <- newIORef []
        sequence
            [ do
                let expected = str i
                    actual = show (docshunt i)
                if expected == actual
                    then return ()
                    else modifyIORef faileds_ref (\faileds -> faileds ++ [i])
            | i <- [1 .. ea]
            ]
        faileds <- readIORef faileds_ref
        if null faileds
            then shelly (">>> " ++ "\"ALL CASES PASSED.\"")
            else shelly (">>> " ++ "({" ++ shows (length faileds) ("}-cases-failed={\n      " ++ showList faileds "\n    })."))
        return ()

testDocIsMonoid :: IO ()
testDocIsMonoid = quickBatch (monoid doc) where
    doc :: Doc
    doc = undefined
