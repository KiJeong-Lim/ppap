module Json.JsonParser where

import Json.JsonLexer
import qualified Control.Monad.Trans.Class as Y
import qualified Control.Monad.Trans.Except as Y
import qualified Control.Monad.Trans.State.Strict as Y
import qualified Data.Map.Strict as YMap
import qualified Data.Set as YSet

data ValueRep
    = ValueRep_object ObjectRep
    | ValueRep_array ArrayRep
    | ValueRep_string String
    | ValueRep_number NumberRep
    | ValueRep_true
    | ValueRep_false
    | ValueRep_null
    deriving (Eq, Show)
type ObjectRep = [(String, ValueRep)]
type ArrayRep = [ValueRep]
data NumberRep
    = NumberRep_integer String
    | NumberRep_fraction String
    | NumberRep_exponent String
    deriving (Eq, Show)

-- the following codes are generated by PGS.

type ParserS = Int

type NSym = Int

type TSym = Int

data Sym
    = NS NSym
    | TS TSym
    deriving (Eq, Ord)

data Action
    = Shift ParserS
    | Reduce (NSym, [Sym])
    | Accept
    deriving (Eq)

data LR1Parser
    = LR1Parser
        { getInitialS :: ParserS
        , getActionTable :: YMap.Map (ParserS, TSym) Action
        , getReduceTable :: YMap.Map (ParserS, NSym) ParserS
        }
    deriving ()

data ParsingTree
    = PTLeaf (JsonToken (Int, Int))
    | PTBranch NSym [ParsingTree]
    deriving ()

jsonparser :: [JsonToken (Int, Int)] -> Either (Maybe (JsonToken (Int, Int))) (ValueRep)
jsonparser = fmap (getValue) . runLALR1 theLALR1Parser where
    getValue :: ParsingTree -> (ValueRep)
    getValue (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[2]] = ValueRep_object (getObject _1)
    getValue (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[4]] = ValueRep_array (getArray _1)
    getValue (PTBranch _ [PTLeaf (T_string loc_1 str_1)])
        | otherwise = ValueRep_string (str_1)
    getValue (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[6]] = ValueRep_number (getNumber _1)
    getValue (PTBranch _ [PTLeaf (T_true loc_1)])
        | otherwise = ValueRep_true
    getValue (PTBranch _ [PTLeaf (T_false loc_1)])
        | otherwise = ValueRep_false
    getValue (PTBranch _ [PTLeaf (T_null loc_1)])
        | otherwise = ValueRep_null
    getObject :: ParsingTree -> (ObjectRep)
    getObject (PTBranch _ [PTLeaf (T_lbrace loc_1), PTLeaf (T_rbrace loc_2)])
        | otherwise = []
    getObject (PTBranch _ [PTLeaf (T_lbrace loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rbrace loc_3)])
        | [guard2] `elem` [[3]] = (getElements _2) 
    getElements :: ParsingTree -> ([(String, ValueRep)])
    getElements (PTBranch _ [PTLeaf (T_string loc_1 str_1), PTLeaf (T_semicolon loc_2), _3@(PTBranch guard3 _)])
        | [guard3] `elem` [[1]] = [((str_1), (getValue _3))]
    getElements (PTBranch _ [PTLeaf (T_string loc_1 str_1), PTLeaf (T_semicolon loc_2), _3@(PTBranch guard3 _), PTLeaf (T_comma loc_4), _5@(PTBranch guard5 _)])
        | [guard3, guard5] `elem` [[1, 3]] = ((str_1), (getValue _3)) : (getElements _5)
    getArray :: ParsingTree -> (ArrayRep)
    getArray (PTBranch _ [PTLeaf (T_lbracket loc_1), PTLeaf (T_rbracket loc_2)])
        | otherwise = []
    getArray (PTBranch _ [PTLeaf (T_lbracket loc_1), _2@(PTBranch guard2 _), PTLeaf (T_rbracket loc_3)])
        | [guard2] `elem` [[5]] = (getMembers _2)
    getMembers :: ParsingTree -> ([ValueRep])
    getMembers (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[1]] = (getValue _1) : []
    getMembers (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (T_comma loc_2), _3@(PTBranch guard3 _)])
        | [guard1, guard3] `elem` [[1, 5]] = (getValue _1) : (getMembers _3)
    getNumber :: ParsingTree -> (NumberRep)
    getNumber (PTBranch _ [PTLeaf (T_integer loc_1 num_1)])
        | otherwise = NumberRep_integer (num_1)
    getNumber (PTBranch _ [PTLeaf (T_fraction loc_1 num_1)])
        | otherwise = NumberRep_fraction (num_1)
    getNumber (PTBranch _ [PTLeaf (T_exponent loc_1 num_1)])
        | otherwise = NumberRep_exponent (num_1)
    toTerminal :: (JsonToken (Int, Int)) -> TSym
    toTerminal (T_lbrace loc) = 1
    toTerminal (T_rbrace loc) = 2
    toTerminal (T_lbracket loc) = 3
    toTerminal (T_rbracket loc) = 4
    toTerminal (T_comma loc) = 5
    toTerminal (T_semicolon loc) = 6
    toTerminal (T_true loc) = 7
    toTerminal (T_false loc) = 8
    toTerminal (T_null loc) = 9
    toTerminal (T_string loc str) = 10
    toTerminal (T_integer loc num) = 11
    toTerminal (T_fraction loc num) = 12
    toTerminal (T_exponent loc num) = 13
    runLALR1 :: LR1Parser -> [JsonToken (Int, Int)] -> Either (Maybe (JsonToken (Int, Int))) ParsingTree
    runLALR1 (LR1Parser getInitS getActionT getReduceT) = go where
        loop inputs = do
            let cur = if null inputs then 0 else toTerminal (head inputs)
                exception = Y.lift (if null inputs then Left Nothing else Left (Just (head inputs)))
            (stack, trees) <- Y.get
            case YMap.lookup (head stack, cur) getActionT of
                Nothing -> exception
                Just Accept -> return ()
                Just (Shift top') -> do
                    Y.put (top' : stack, PTLeaf (head inputs) : trees)
                    loop (tail inputs)
                Just (Reduce (lhs, rhs)) -> do
                    let n = length rhs
                    case YMap.lookup (stack !! n, lhs) getReduceT of
                        Nothing -> exception
                        Just top' -> do
                            Y.put (top' : drop n stack, PTBranch lhs (reverse (take n trees)) : drop n trees)
                            loop inputs
        go tokens = do
            (_, (_, result)) <- Y.runStateT (loop tokens) ([getInitS], [])
            case result of
                [output] -> return output
    theLALR1Parser :: LR1Parser
    theLALR1Parser = LR1Parser
        { getInitialS = 0
        , getActionTable = YMap.fromAscList 
            [ ((0, 1), Shift 9), ((0, 3), Shift 10), ((0, 7), Shift 13), ((0, 8), Shift 6), ((0, 9), Shift 11), ((0, 10), Shift 12), ((0, 11), Shift 8), ((0, 12), Shift 7), ((0, 13), Shift 5)
            , ((1, 0), Reduce (1, [NS 4])), ((1, 2), Reduce (1, [NS 4])), ((1, 4), Reduce (1, [NS 4])), ((1, 5), Reduce (1, [NS 4]))
            , ((2, 0), Reduce (1, [NS 6])), ((2, 2), Reduce (1, [NS 6])), ((2, 4), Reduce (1, [NS 6])), ((2, 5), Reduce (1, [NS 6]))
            , ((3, 0), Reduce (1, [NS 2])), ((3, 2), Reduce (1, [NS 2])), ((3, 4), Reduce (1, [NS 2])), ((3, 5), Reduce (1, [NS 2]))
            , ((4, 0), Accept)
            , ((5, 0), Reduce (6, [TS 13])), ((5, 2), Reduce (6, [TS 13])), ((5, 4), Reduce (6, [TS 13])), ((5, 5), Reduce (6, [TS 13]))
            , ((6, 0), Reduce (1, [TS 8])), ((6, 2), Reduce (1, [TS 8])), ((6, 4), Reduce (1, [TS 8])), ((6, 5), Reduce (1, [TS 8]))
            , ((7, 0), Reduce (6, [TS 12])), ((7, 2), Reduce (6, [TS 12])), ((7, 4), Reduce (6, [TS 12])), ((7, 5), Reduce (6, [TS 12]))
            , ((8, 0), Reduce (6, [TS 11])), ((8, 2), Reduce (6, [TS 11])), ((8, 4), Reduce (6, [TS 11])), ((8, 5), Reduce (6, [TS 11]))
            , ((9, 2), Shift 18), ((9, 10), Shift 19)
            , ((10, 1), Shift 9), ((10, 3), Shift 10), ((10, 4), Shift 16), ((10, 7), Shift 13), ((10, 8), Shift 6), ((10, 9), Shift 11), ((10, 10), Shift 12), ((10, 11), Shift 8), ((10, 12), Shift 7), ((10, 13), Shift 5)
            , ((11, 0), Reduce (1, [TS 9])), ((11, 2), Reduce (1, [TS 9])), ((11, 4), Reduce (1, [TS 9])), ((11, 5), Reduce (1, [TS 9]))
            , ((12, 0), Reduce (1, [TS 10])), ((12, 2), Reduce (1, [TS 10])), ((12, 4), Reduce (1, [TS 10])), ((12, 5), Reduce (1, [TS 10]))
            , ((13, 0), Reduce (1, [TS 7])), ((13, 2), Reduce (1, [TS 7])), ((13, 4), Reduce (1, [TS 7])), ((13, 5), Reduce (1, [TS 7]))
            , ((14, 4), Shift 20)
            , ((15, 4), Reduce (5, [NS 1])), ((15, 5), Shift 22)
            , ((16, 0), Reduce (4, [TS 3, TS 4])), ((16, 2), Reduce (4, [TS 3, TS 4])), ((16, 4), Reduce (4, [TS 3, TS 4])), ((16, 5), Reduce (4, [TS 3, TS 4]))
            , ((17, 2), Shift 23)
            , ((18, 0), Reduce (2, [TS 1, TS 2])), ((18, 2), Reduce (2, [TS 1, TS 2])), ((18, 4), Reduce (2, [TS 1, TS 2])), ((18, 5), Reduce (2, [TS 1, TS 2]))
            , ((19, 6), Shift 21)
            , ((20, 0), Reduce (4, [TS 3, NS 5, TS 4])), ((20, 2), Reduce (4, [TS 3, NS 5, TS 4])), ((20, 4), Reduce (4, [TS 3, NS 5, TS 4])), ((20, 5), Reduce (4, [TS 3, NS 5, TS 4]))
            , ((21, 1), Shift 9), ((21, 3), Shift 10), ((21, 7), Shift 13), ((21, 8), Shift 6), ((21, 9), Shift 11), ((21, 10), Shift 12), ((21, 11), Shift 8), ((21, 12), Shift 7), ((21, 13), Shift 5)
            , ((22, 1), Shift 9), ((22, 3), Shift 10), ((22, 7), Shift 13), ((22, 8), Shift 6), ((22, 9), Shift 11), ((22, 10), Shift 12), ((22, 11), Shift 8), ((22, 12), Shift 7), ((22, 13), Shift 5)
            , ((23, 0), Reduce (2, [TS 1, NS 3, TS 2])), ((23, 2), Reduce (2, [TS 1, NS 3, TS 2])), ((23, 4), Reduce (2, [TS 1, NS 3, TS 2])), ((23, 5), Reduce (2, [TS 1, NS 3, TS 2]))
            , ((24, 2), Reduce (3, [TS 10, TS 6, NS 1])), ((24, 5), Shift 26)
            , ((25, 4), Reduce (5, [NS 1, TS 5, NS 5]))
            , ((26, 10), Shift 19)
            , ((27, 2), Reduce (3, [TS 10, TS 6, NS 1, TS 5, NS 3]))
            ]
        , getReduceTable = YMap.fromAscList 
            [ ((0, 1), 4), ((0, 2), 3), ((0, 4), 1), ((0, 6), 2)
            , ((9, 3), 17)
            , ((10, 1), 15), ((10, 2), 3), ((10, 4), 1), ((10, 5), 14), ((10, 6), 2)
            , ((21, 1), 24), ((21, 2), 3), ((21, 4), 1), ((21, 6), 2)
            , ((22, 1), 15), ((22, 2), 3), ((22, 4), 1), ((22, 5), 25), ((22, 6), 2)
            , ((26, 3), 27)
            ]
        }

{- The canonical collection of LR(0) items is:
getParserSInfo :: ParserS -> ParserSInfo
getParserSInfo 0 = ParserSInfo
    { myItems = 
        [ "<Array> ::= . `lbracket' <Members> `rbracket'"
        , "<Array> ::= . `lbracket' `rbracket'"
        , "<Number> ::= . `explit'"
        , "<Number> ::= . `fralit'"
        , "<Number> ::= . `intlit'"
        , "<Object> ::= . `lbrace' <Elements> `rbrace'"
        , "<Object> ::= . `lbrace' `rbrace'"
        , "<Value> ::= . <Array>"
        , "<Value> ::= . <Number>"
        , "<Value> ::= . <Object>"
        , "<Value> ::= . `false'"
        , "<Value> ::= . `null'"
        , "<Value> ::= . `strlit'"
        , "<Value> ::= . `true'"
        , "<\\ACCEPT> ::= . <Value> `\\$'"
        ]
    , myNexts = 
        [ "<Array> +-> 1"
        , "<Number> +-> 2"
        , "<Object> +-> 3"
        , "<Value> +-> 4"
        , "`explit' +-> 5"
        , "`false' +-> 6"
        , "`fralit' +-> 7"
        , "`intlit' +-> 8"
        , "`lbrace' +-> 9"
        , "`lbracket' +-> 10"
        , "`null' +-> 11"
        , "`strlit' +-> 12"
        , "`true' +-> 13"
        ]
    }
getParserSInfo 1 = ParserSInfo
    { myItems = 
        [ "<Value> ::= <Array> ."
        ]
    , myNexts = []
    }
getParserSInfo 2 = ParserSInfo
    { myItems = 
        [ "<Value> ::= <Number> ."
        ]
    , myNexts = []
    }
getParserSInfo 3 = ParserSInfo
    { myItems = 
        [ "<Value> ::= <Object> ."
        ]
    , myNexts = []
    }
getParserSInfo 4 = ParserSInfo
    { myItems = 
        [ "<\\ACCEPT> ::= <Value> . `\\$'"
        ]
    , myNexts = []
    }
getParserSInfo 5 = ParserSInfo
    { myItems = 
        [ "<Number> ::= `explit' ."
        ]
    , myNexts = []
    }
getParserSInfo 6 = ParserSInfo
    { myItems = 
        [ "<Value> ::= `false' ."
        ]
    , myNexts = []
    }
getParserSInfo 7 = ParserSInfo
    { myItems = 
        [ "<Number> ::= `fralit' ."
        ]
    , myNexts = []
    }
getParserSInfo 8 = ParserSInfo
    { myItems = 
        [ "<Number> ::= `intlit' ."
        ]
    , myNexts = []
    }
getParserSInfo 9 = ParserSInfo
    { myItems = 
        [ "<Elements> ::= . `strlit' `semicolon' <Value>"
        , "<Elements> ::= . `strlit' `semicolon' <Value> `comma' <Elements>"
        , "<Object> ::= `lbrace' . <Elements> `rbrace'"
        , "<Object> ::= `lbrace' . `rbrace'"
        ]
    , myNexts = 
        [ "<Elements> +-> 17"
        , "`rbrace' +-> 18"
        , "`strlit' +-> 19"
        ]
    }
getParserSInfo 10 = ParserSInfo
    { myItems = 
        [ "<Array> ::= . `lbracket' <Members> `rbracket'"
        , "<Array> ::= . `lbracket' `rbracket'"
        , "<Array> ::= `lbracket' . <Members> `rbracket'"
        , "<Array> ::= `lbracket' . `rbracket'"
        , "<Members> ::= . <Value>"
        , "<Members> ::= . <Value> `comma' <Members>"
        , "<Number> ::= . `explit'"
        , "<Number> ::= . `fralit'"
        , "<Number> ::= . `intlit'"
        , "<Object> ::= . `lbrace' <Elements> `rbrace'"
        , "<Object> ::= . `lbrace' `rbrace'"
        , "<Value> ::= . <Array>"
        , "<Value> ::= . <Number>"
        , "<Value> ::= . <Object>"
        , "<Value> ::= . `false'"
        , "<Value> ::= . `null'"
        , "<Value> ::= . `strlit'"
        , "<Value> ::= . `true'"
        ]
    , myNexts = 
        [ "<Array> +-> 1"
        , "<Number> +-> 2"
        , "<Object> +-> 3"
        , "`explit' +-> 5"
        , "`false' +-> 6"
        , "`fralit' +-> 7"
        , "`intlit' +-> 8"
        , "`lbrace' +-> 9"
        , "`lbracket' +-> 10"
        , "`null' +-> 11"
        , "`strlit' +-> 12"
        , "`true' +-> 13"
        , "<Members> +-> 14"
        , "<Value> +-> 15"
        , "`rbracket' +-> 16"
        ]
    }
getParserSInfo 11 = ParserSInfo
    { myItems = 
        [ "<Value> ::= `null' ."
        ]
    , myNexts = []
    }
getParserSInfo 12 = ParserSInfo
    { myItems = 
        [ "<Value> ::= `strlit' ."
        ]
    , myNexts = []
    }
getParserSInfo 13 = ParserSInfo
    { myItems = 
        [ "<Value> ::= `true' ."
        ]
    , myNexts = []
    }
getParserSInfo 14 = ParserSInfo
    { myItems = 
        [ "<Array> ::= `lbracket' <Members> . `rbracket'"
        ]
    , myNexts = 
        [ "`rbracket' +-> 20"
        ]
    }
getParserSInfo 15 = ParserSInfo
    { myItems = 
        [ "<Members> ::= <Value> ."
        , "<Members> ::= <Value> . `comma' <Members>"
        ]
    , myNexts = 
        [ "`comma' +-> 22"
        ]
    }
getParserSInfo 16 = ParserSInfo
    { myItems = 
        [ "<Array> ::= `lbracket' `rbracket' ."
        ]
    , myNexts = []
    }
getParserSInfo 17 = ParserSInfo
    { myItems = 
        [ "<Object> ::= `lbrace' <Elements> . `rbrace'"
        ]
    , myNexts = 
        [ "`rbrace' +-> 23"
        ]
    }
getParserSInfo 18 = ParserSInfo
    { myItems = 
        [ "<Object> ::= `lbrace' `rbrace' ."
        ]
    , myNexts = []
    }
getParserSInfo 19 = ParserSInfo
    { myItems = 
        [ "<Elements> ::= `strlit' . `semicolon' <Value>"
        , "<Elements> ::= `strlit' . `semicolon' <Value> `comma' <Elements>"
        ]
    , myNexts = 
        [ "`semicolon' +-> 21"
        ]
    }
getParserSInfo 20 = ParserSInfo
    { myItems = 
        [ "<Array> ::= `lbracket' <Members> `rbracket' ."
        ]
    , myNexts = []
    }
getParserSInfo 21 = ParserSInfo
    { myItems = 
        [ "<Array> ::= . `lbracket' <Members> `rbracket'"
        , "<Array> ::= . `lbracket' `rbracket'"
        , "<Elements> ::= `strlit' `semicolon' . <Value>"
        , "<Elements> ::= `strlit' `semicolon' . <Value> `comma' <Elements>"
        , "<Number> ::= . `explit'"
        , "<Number> ::= . `fralit'"
        , "<Number> ::= . `intlit'"
        , "<Object> ::= . `lbrace' <Elements> `rbrace'"
        , "<Object> ::= . `lbrace' `rbrace'"
        , "<Value> ::= . <Array>"
        , "<Value> ::= . <Number>"
        , "<Value> ::= . <Object>"
        , "<Value> ::= . `false'"
        , "<Value> ::= . `null'"
        , "<Value> ::= . `strlit'"
        , "<Value> ::= . `true'"
        ]
    , myNexts = 
        [ "<Array> +-> 1"
        , "<Number> +-> 2"
        , "<Object> +-> 3"
        , "`explit' +-> 5"
        , "`false' +-> 6"
        , "`fralit' +-> 7"
        , "`intlit' +-> 8"
        , "`lbrace' +-> 9"
        , "`lbracket' +-> 10"
        , "`null' +-> 11"
        , "`strlit' +-> 12"
        , "`true' +-> 13"
        , "<Value> +-> 24"
        ]
    }
getParserSInfo 22 = ParserSInfo
    { myItems = 
        [ "<Array> ::= . `lbracket' <Members> `rbracket'"
        , "<Array> ::= . `lbracket' `rbracket'"
        , "<Members> ::= . <Value>"
        , "<Members> ::= . <Value> `comma' <Members>"
        , "<Members> ::= <Value> `comma' . <Members>"
        , "<Number> ::= . `explit'"
        , "<Number> ::= . `fralit'"
        , "<Number> ::= . `intlit'"
        , "<Object> ::= . `lbrace' <Elements> `rbrace'"
        , "<Object> ::= . `lbrace' `rbrace'"
        , "<Value> ::= . <Array>"
        , "<Value> ::= . <Number>"
        , "<Value> ::= . <Object>"
        , "<Value> ::= . `false'"
        , "<Value> ::= . `null'"
        , "<Value> ::= . `strlit'"
        , "<Value> ::= . `true'"
        ]
    , myNexts = 
        [ "<Array> +-> 1"
        , "<Number> +-> 2"
        , "<Object> +-> 3"
        , "`explit' +-> 5"
        , "`false' +-> 6"
        , "`fralit' +-> 7"
        , "`intlit' +-> 8"
        , "`lbrace' +-> 9"
        , "`lbracket' +-> 10"
        , "`null' +-> 11"
        , "`strlit' +-> 12"
        , "`true' +-> 13"
        , "<Value> +-> 15"
        , "<Members> +-> 25"
        ]
    }
getParserSInfo 23 = ParserSInfo
    { myItems = 
        [ "<Object> ::= `lbrace' <Elements> `rbrace' ."
        ]
    , myNexts = []
    }
getParserSInfo 24 = ParserSInfo
    { myItems = 
        [ "<Elements> ::= `strlit' `semicolon' <Value> ."
        , "<Elements> ::= `strlit' `semicolon' <Value> . `comma' <Elements>"
        ]
    , myNexts = 
        [ "`comma' +-> 26"
        ]
    }
getParserSInfo 25 = ParserSInfo
    { myItems = 
        [ "<Members> ::= <Value> `comma' <Members> ."
        ]
    , myNexts = []
    }
getParserSInfo 26 = ParserSInfo
    { myItems = 
        [ "<Elements> ::= . `strlit' `semicolon' <Value>"
        , "<Elements> ::= . `strlit' `semicolon' <Value> `comma' <Elements>"
        , "<Elements> ::= `strlit' `semicolon' <Value> `comma' . <Elements>"
        ]
    , myNexts = 
        [ "`strlit' +-> 19"
        , "<Elements> +-> 27"
        ]
    }
getParserSInfo 27 = ParserSInfo
    { myItems = 
        [ "<Elements> ::= `strlit' `semicolon' <Value> `comma' <Elements> ."
        ]
    , myNexts = []
    }
-}
