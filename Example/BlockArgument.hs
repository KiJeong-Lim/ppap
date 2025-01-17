module BlockArgument where
import qualified Control.Monad.Trans.Class as Y
import qualified Control.Monad.Trans.Except as Y
import qualified Control.Monad.Trans.State.Strict as Y
import qualified Data.Map.Strict as YMap
import qualified Data.Set as YSet

data Tok
    = LargeId String
    | SmallId String
    | LParen
    | RParen
    | Lambda
    deriving (Eq, Ord, Show)

data Term
    = Lam String Term
    | App Term Term
    | Var String
    deriving (Eq, Ord, Show)

main :: IO ()
main = do
    let example = [SmallId "sigma", LargeId "X", Lambda, SmallId "p", LargeId "X", LParen, SmallId "q", LargeId "X", RParen]
    print (parser example)

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
    = PTLeaf (Tok)
    | PTBranch NSym [ParsingTree]
    deriving ()

parser :: [Tok] -> Either (Maybe (Tok)) (Term)
parser = fmap (getTerm0) . runLALR1 theLALR1Parser where
    getTerm0 :: ParsingTree -> (Term)
    getTerm0 (PTBranch _ [PTLeaf (LargeId nm_1), PTLeaf (Lambda), _3@(PTBranch guard3 _)])
        | [guard3] `elem` [[1]] = Lam (nm_1) (getTerm0 _3)
    getTerm0 (PTBranch _ [PTLeaf (SmallId nm_1), PTLeaf (Lambda), _3@(PTBranch guard3 _)])
        | [guard3] `elem` [[1]] = Lam (nm_1) (getTerm0 _3)
    getTerm0 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[2]] = (getTerm1 _1)
    getTerm1 :: ParsingTree -> (Term)
    getTerm1 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (LargeId nm_2), PTLeaf (Lambda), _4@(PTBranch guard4 _)])
        | [guard1, guard4] `elem` [[3, 1]] = App (getTerm2 _1) (Lam (nm_2) (getTerm0 _4))
    getTerm1 (PTBranch _ [_1@(PTBranch guard1 _), PTLeaf (SmallId nm_2), PTLeaf (Lambda), _4@(PTBranch guard4 _)])
        | [guard1, guard4] `elem` [[3, 1]] = App (getTerm2 _1) (Lam (nm_2) (getTerm0 _4))
    getTerm1 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[3]] = (getTerm2 _1)
    getTerm2 :: ParsingTree -> (Term)
    getTerm2 (PTBranch _ [_1@(PTBranch guard1 _), _2@(PTBranch guard2 _)])
        | [guard1, guard2] `elem` [[3, 4]] = App (getTerm2 _1) (getTerm3 _2)
    getTerm2 (PTBranch _ [_1@(PTBranch guard1 _)])
        | [guard1] `elem` [[4]] = (getTerm3 _1)
    getTerm3 :: ParsingTree -> (Term)
    getTerm3 (PTBranch _ [PTLeaf (LargeId nm_1)])
        | otherwise = Var (nm_1)
    getTerm3 (PTBranch _ [PTLeaf (SmallId nm_1)])
        | otherwise = Var (nm_1)
    getTerm3 (PTBranch _ [PTLeaf (LParen), _2@(PTBranch guard2 _), PTLeaf (RParen)])
        | [guard2] `elem` [[1]] = (getTerm0 _2)
    toTerminal :: (Tok) -> TSym
    toTerminal (LargeId nm) = 1
    toTerminal (SmallId nm) = 2
    toTerminal (LParen) = 3
    toTerminal (RParen) = 4
    toTerminal (Lambda) = 5
    runLALR1 :: LR1Parser -> [Tok] -> Either (Maybe (Tok)) ParsingTree
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
            [ ((0, 1), Shift 5), ((0, 2), Shift 7), ((0, 3), Shift 6)
            , ((1, 0), Accept)
            , ((2, 0), Reduce (1, [NS 2])), ((2, 4), Reduce (1, [NS 2]))
            , ((3, 0), Reduce (2, [NS 3])), ((3, 1), Shift 12), ((3, 2), Shift 13), ((3, 3), Shift 6), ((3, 4), Reduce (2, [NS 3]))
            , ((4, 0), Reduce (3, [NS 4])), ((4, 1), Reduce (3, [NS 4])), ((4, 2), Reduce (3, [NS 4])), ((4, 3), Reduce (3, [NS 4])), ((4, 4), Reduce (3, [NS 4]))
            , ((5, 0), Reduce (4, [TS 1])), ((5, 1), Reduce (4, [TS 1])), ((5, 2), Reduce (4, [TS 1])), ((5, 3), Reduce (4, [TS 1])), ((5, 4), Reduce (4, [TS 1])), ((5, 5), Shift 9)
            , ((6, 1), Shift 5), ((6, 2), Shift 7), ((6, 3), Shift 6)
            , ((7, 0), Reduce (4, [TS 2])), ((7, 1), Reduce (4, [TS 2])), ((7, 2), Reduce (4, [TS 2])), ((7, 3), Reduce (4, [TS 2])), ((7, 4), Reduce (4, [TS 2])), ((7, 5), Shift 10)
            , ((8, 4), Shift 18)
            , ((9, 1), Shift 5), ((9, 2), Shift 7), ((9, 3), Shift 6)
            , ((10, 1), Shift 5), ((10, 2), Shift 7), ((10, 3), Shift 6)
            , ((11, 0), Reduce (3, [NS 3, NS 4])), ((11, 1), Reduce (3, [NS 3, NS 4])), ((11, 2), Reduce (3, [NS 3, NS 4])), ((11, 3), Reduce (3, [NS 3, NS 4])), ((11, 4), Reduce (3, [NS 3, NS 4]))
            , ((12, 0), Reduce (4, [TS 1])), ((12, 1), Reduce (4, [TS 1])), ((12, 2), Reduce (4, [TS 1])), ((12, 3), Reduce (4, [TS 1])), ((12, 4), Reduce (4, [TS 1])), ((12, 5), Shift 16)
            , ((13, 0), Reduce (4, [TS 2])), ((13, 1), Reduce (4, [TS 2])), ((13, 2), Reduce (4, [TS 2])), ((13, 3), Reduce (4, [TS 2])), ((13, 4), Reduce (4, [TS 2])), ((13, 5), Shift 17)
            , ((14, 0), Reduce (1, [TS 1, TS 5, NS 1])), ((14, 4), Reduce (1, [TS 1, TS 5, NS 1]))
            , ((15, 0), Reduce (1, [TS 2, TS 5, NS 1])), ((15, 4), Reduce (1, [TS 2, TS 5, NS 1]))
            , ((16, 1), Shift 5), ((16, 2), Shift 7), ((16, 3), Shift 6)
            , ((17, 1), Shift 5), ((17, 2), Shift 7), ((17, 3), Shift 6)
            , ((18, 0), Reduce (4, [TS 3, NS 1, TS 4])), ((18, 1), Reduce (4, [TS 3, NS 1, TS 4])), ((18, 2), Reduce (4, [TS 3, NS 1, TS 4])), ((18, 3), Reduce (4, [TS 3, NS 1, TS 4])), ((18, 4), Reduce (4, [TS 3, NS 1, TS 4]))
            , ((19, 0), Reduce (2, [NS 3, TS 1, TS 5, NS 1])), ((19, 4), Reduce (2, [NS 3, TS 1, TS 5, NS 1]))
            , ((20, 0), Reduce (2, [NS 3, TS 2, TS 5, NS 1])), ((20, 4), Reduce (2, [NS 3, TS 2, TS 5, NS 1]))
            ]
        , getReduceTable = YMap.fromAscList 
            [ ((0, 1), 1), ((0, 2), 2), ((0, 3), 3), ((0, 4), 4)
            , ((3, 4), 11)
            , ((6, 1), 8), ((6, 2), 2), ((6, 3), 3), ((6, 4), 4)
            , ((9, 1), 14), ((9, 2), 2), ((9, 3), 3), ((9, 4), 4)
            , ((10, 1), 15), ((10, 2), 2), ((10, 3), 3), ((10, 4), 4)
            , ((16, 1), 19), ((16, 2), 2), ((16, 3), 3), ((16, 4), 4)
            , ((17, 1), 20), ((17, 2), 2), ((17, 3), 3), ((17, 4), 4)
            ]
        }

{-
getParserSInfo :: ParserS -> ParserSInfo
getParserSInfo 0 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        , "<\\ACCEPT> ::= . <Term0> `\\$'"
        ]
    , myNexts = 
        [ "<Term0> +-> 1"
        , "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        ]
    }
getParserSInfo 1 = ParserSInfo
    { myItems = 
        [ "<\\ACCEPT> ::= <Term0> . `\\$'"
        ]
    , myNexts = []
    }
getParserSInfo 2 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= <Term1> ."
        ]
    , myNexts = []
    }
getParserSInfo 3 = ParserSInfo
    { myItems = 
        [ "<Term1> ::= <Term2> ."
        , "<Term1> ::= <Term2> . `lid' `lambda' <Term0>"
        , "<Term1> ::= <Term2> . `sid' `lambda' <Term0>"
        , "<Term2> ::= <Term2> . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        ]
    , myNexts = 
        [ "`lprn' +-> 6"
        , "<Term3> +-> 11"
        , "`lid' +-> 12"
        , "`sid' +-> 13"
        ]
    }
getParserSInfo 4 = ParserSInfo
    { myItems = 
        [ "<Term2> ::= <Term3> ."
        ]
    , myNexts = []
    }
getParserSInfo 5 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= `lid' . `lambda' <Term0>"
        , "<Term3> ::= `lid' ."
        ]
    , myNexts = 
        [ "`lambda' +-> 9"
        ]
    }
getParserSInfo 6 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        , "<Term3> ::= `lprn' . <Term0> `rprn'"
        ]
    , myNexts = 
        [ "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        , "<Term0> +-> 8"
        ]
    }
getParserSInfo 7 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= `sid' . `lambda' <Term0>"
        , "<Term3> ::= `sid' ."
        ]
    , myNexts = 
        [ "`lambda' +-> 10"
        ]
    }
getParserSInfo 8 = ParserSInfo
    { myItems = 
        [ "<Term3> ::= `lprn' <Term0> . `rprn'"
        ]
    , myNexts = 
        [ "`rprn' +-> 18"
        ]
    }
getParserSInfo 9 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term0> ::= `lid' `lambda' . <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        ]
    , myNexts = 
        [ "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        , "<Term0> +-> 14"
        ]
    }
getParserSInfo 10 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term0> ::= `sid' `lambda' . <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        ]
    , myNexts = 
        [ "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        , "<Term0> +-> 15"
        ]
    }
getParserSInfo 11 = ParserSInfo
    { myItems = 
        [ "<Term2> ::= <Term2> <Term3> ."
        ]
    , myNexts = []
    }
getParserSInfo 12 = ParserSInfo
    { myItems = 
        [ "<Term1> ::= <Term2> `lid' . `lambda' <Term0>"
        , "<Term3> ::= `lid' ."
        ]
    , myNexts = 
        [ "`lambda' +-> 16"
        ]
    }
getParserSInfo 13 = ParserSInfo
    { myItems = 
        [ "<Term1> ::= <Term2> `sid' . `lambda' <Term0>"
        , "<Term3> ::= `sid' ."
        ]
    , myNexts = 
        [ "`lambda' +-> 17"
        ]
    }
getParserSInfo 14 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= `lid' `lambda' <Term0> ."
        ]
    , myNexts = []
    }
getParserSInfo 15 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= `sid' `lambda' <Term0> ."
        ]
    , myNexts = []
    }
getParserSInfo 16 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term1> ::= <Term2> `lid' `lambda' . <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        ]
    , myNexts = 
        [ "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        , "<Term0> +-> 19"
        ]
    }
getParserSInfo 17 = ParserSInfo
    { myItems = 
        [ "<Term0> ::= . <Term1>"
        , "<Term0> ::= . `lid' `lambda' <Term0>"
        , "<Term0> ::= . `sid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2>"
        , "<Term1> ::= . <Term2> `lid' `lambda' <Term0>"
        , "<Term1> ::= . <Term2> `sid' `lambda' <Term0>"
        , "<Term1> ::= <Term2> `sid' `lambda' . <Term0>"
        , "<Term2> ::= . <Term2> <Term3>"
        , "<Term2> ::= . <Term3>"
        , "<Term3> ::= . `lid'"
        , "<Term3> ::= . `lprn' <Term0> `rprn'"
        , "<Term3> ::= . `sid'"
        ]
    , myNexts = 
        [ "<Term1> +-> 2"
        , "<Term2> +-> 3"
        , "<Term3> +-> 4"
        , "`lid' +-> 5"
        , "`lprn' +-> 6"
        , "`sid' +-> 7"
        , "<Term0> +-> 20"
        ]
    }
getParserSInfo 18 = ParserSInfo
    { myItems = 
        [ "<Term3> ::= `lprn' <Term0> `rprn' ."
        ]
    , myNexts = []
    }
getParserSInfo 19 = ParserSInfo
    { myItems = 
        [ "<Term1> ::= <Term2> `lid' `lambda' <Term0> ."
        ]
    , myNexts = []
    }
getParserSInfo 20 = ParserSInfo
    { myItems = 
        [ "<Term1> ::= <Term2> `sid' `lambda' <Term0> ."
        ]
    , myNexts = []
    }
_First = 
    [ "<Term0> +-> {`lid', `lprn', `sid'}"
    , "<Term1> +-> {`lid', `lprn', `sid'}"
    , "<Term2> +-> {`lid', `lprn', `sid'}"
    , "<Term3> +-> {`lid', `lprn', `sid'}"
    , "<\\ACCEPT> +-> {`lid', `lprn', `sid'}"
    ]
_LA = 
    [ "( q = 1, [<\\ACCEPT> ::= <Term0> `\\$'] ) +-> {`\\$'}"
    , "( q = 2, [<Term0> ::= <Term1>] ) +-> {`\\$', `rprn'}"
    , "( q = 3, [<Term1> ::= <Term2>] ) +-> {`\\$', `rprn'}"
    , "( q = 4, [<Term2> ::= <Term3>] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 5, [<Term3> ::= `lid'] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 7, [<Term3> ::= `sid'] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 11, [<Term2> ::= <Term2> <Term3>] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 12, [<Term3> ::= `lid'] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 13, [<Term3> ::= `sid'] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 14, [<Term0> ::= `lid' `lambda' <Term0>] ) +-> {`\\$', `rprn'}"
    , "( q = 15, [<Term0> ::= `sid' `lambda' <Term0>] ) +-> {`\\$', `rprn'}"
    , "( q = 18, [<Term3> ::= `lprn' <Term0> `rprn'] ) +-> {`\\$', `lid', `lprn', `rprn', `sid'}"
    , "( q = 19, [<Term1> ::= <Term2> `lid' `lambda' <Term0>] ) +-> {`\\$', `rprn'}"
    , "( q = 20, [<Term1> ::= <Term2> `sid' `lambda' <Term0>] ) +-> {`\\$', `rprn'}"
    ]
-}
