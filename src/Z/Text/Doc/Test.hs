module Z.Text.Doc.Test where

import Data.IORef
import Z.Text.Doc

testDoc :: IO ()
testDoc = go 5 where
    doc :: Int -> Doc
    doc 1 = vcat
        [ beam '-'
        , hcat
            [ beam '|'
            , pstr " "
            , plist
                [ pstr "Point" +> pnl +> pparen True "\t{ " "\n\t}" (ppunc (pnl +> pstr "\t, ") [pstr "x = " +> pprint 1, pstr "y = " +> pprint 2])
                , pstr "Point " +> pparen True "{ " " }" (ppunc (pstr ", ") [pstr "x = " +> pprint 3, pstr "y = " +> pprint 4])
                ]
            ]
        , beam '^'
        ]
    doc 2 = vcat []
    doc 3 = hcat []
    doc 4 = pcat []
    doc 5 = vcat
        [ beam '-'
        , pstr " "
        , beam '-'
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
    go :: Int -> IO ()
    go ea = do
        faileds_ref <- newIORef []
        sequence
            [ do
                let expected = str i
                    actual = show (doc i)
                if expected == actual
                    then return ()
                    else do
                        faileds <- readIORef faileds_ref
                        writeIORef faileds_ref (faileds ++ [i])
                        return ()
            | i <- [1 .. ea]
            ]
        faileds <- readIORef faileds_ref
        putStrLn (if null faileds then ">>> all cases passed." else ">>> " ++ shows (length faileds) " cases failed: " ++ showList faileds "")
        return ()
