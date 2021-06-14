module Z.Text.Doc.Test where

import Z.Text.Doc

doc1 :: Doc
doc1 = vcat
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

test1 :: Bool
test1 = show doc1 == str where
    str :: String
    str = concat
        [ "--------------------------\n"
        , "| [ Point\n"
        , "|     { x = 1\n"
        , "|     , y = 2\n"
        , "|     }\n"
        , "| , Point { x = 3, y = 4 }\n"
        , "| ]\n"
        , "^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
        ]
