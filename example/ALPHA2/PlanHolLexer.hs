module Hol.ALPHA2.PlanHolLexer where

import Hol.ALPHA2.Header
import Data.Char (isPrint)
import qualified Control.Monad.Trans.State.Strict as XState
import qualified Data.Functor.Identity as XIdentity
import qualified Data.Map.Strict as XMap
import qualified Data.Set as XSet

data Token
    = T_dot SLoc
    | T_arrow SLoc
    | T_lparen SLoc
    | T_rparen SLoc
    | T_lbracket SLoc
    | T_rbracket SLoc
    | T_quest SLoc
    | T_if SLoc
    | T_comma SLoc
    | T_semicolon SLoc
    | T_fatarrow SLoc
    | T_succ SLoc
    | T_eq SLoc
    | T_le SLoc
    | T_lt SLoc
    | T_gt SLoc
    | T_ge SLoc
    | T_plus SLoc
    | T_minus SLoc
    | T_star SLoc
    | T_slash SLoc
    | T_pi SLoc
    | T_sigma SLoc
    | T_cut SLoc
    | T_true SLoc
    | T_fail SLoc
    | T_is SLoc
    | T_debug SLoc
    | T_bslash SLoc
    | T_cons SLoc
    | T_kind SLoc
    | T_type SLoc
    | T_wildcard SLoc
    | T_id SLoc String
    | T_nat_lit SLoc Integer
    | T_chr_lit SLoc Char
    | T_str_lit SLoc String
    | T_lex_error SLoc
    deriving (Show)

data TermRep
    = RVar SLoc LargeId
    | RCon SLoc DataConstructor
    | RApp SLoc TermRep TermRep
    | RAbs SLoc LargeId TermRep
    | RPrn SLoc TermRep
    | R_wc SLoc
    deriving (Show)

data TypeRep
    = RTyVar SLoc LargeId
    | RTyCon SLoc TypeConstructor
    | RTyApp SLoc TypeRep TypeRep
    | RTyPrn SLoc TypeRep
    deriving (Show)

data KindRep
    = RStar SLoc
    | RKArr SLoc KindRep KindRep
    | RKPrn SLoc KindRep
    deriving (Show)

data DeclRep
    = RKindDecl SLoc TypeConstructor KindRep
    | RTypeDecl SLoc DataConstructor TypeRep
    | RFactDecl SLoc TermRep
    deriving (Show)

instance HasSLoc Token where
    getSLoc token = case token of
        T_dot loc -> loc
        T_arrow loc -> loc
        T_lparen loc -> loc
        T_rparen loc -> loc
        T_lbracket loc -> loc
        T_rbracket loc -> loc
        T_if loc -> loc
        T_quest loc -> loc
        T_comma loc -> loc
        T_semicolon loc -> loc
        T_fatarrow loc -> loc
        T_succ loc -> loc
        T_eq loc -> loc
        T_le loc -> loc
        T_lt loc -> loc
        T_gt loc -> loc
        T_ge loc -> loc
        T_plus loc -> loc
        T_minus loc -> loc
        T_star loc -> loc
        T_slash loc -> loc
        T_pi loc -> loc
        T_sigma loc -> loc
        T_cut loc -> loc
        T_true loc -> loc
        T_fail loc -> loc
        T_is loc -> loc
        T_debug loc -> loc
        T_bslash loc -> loc
        T_cons loc -> loc
        T_kind loc -> loc
        T_type loc -> loc
        T_wildcard loc -> loc
        T_id loc _ -> loc
        T_nat_lit loc _ -> loc
        T_chr_lit loc _ -> loc
        T_str_lit loc _ -> loc
        T_lex_error loc -> loc

instance HasSLoc TermRep where
    getSLoc term_rep = case term_rep of
        RVar loc _ -> loc
        RCon loc _ -> loc
        RApp loc _ _ -> loc
        RAbs loc _ _ -> loc
        RPrn loc _ -> loc
        R_wc loc -> loc

instance HasSLoc TypeRep where
    getSLoc type_rep = case type_rep of
        RTyVar loc _ -> loc
        RTyCon loc _ -> loc
        RTyApp loc _ _ -> loc
        RTyPrn loc _ -> loc

instance HasSLoc KindRep where
    getSLoc kind_rep = case kind_rep of
        RStar loc -> loc
        RKArr loc _ _ -> loc
        RKPrn loc _ -> loc

mkNatLit :: SLoc -> Integer -> TermRep
mkNatLit loc nat = RCon loc (DC_NatL nat)

mkChrLit :: SLoc -> Char -> TermRep
mkChrLit loc chr = RCon loc (DC_ChrL chr)

runHolLexer :: String -> Either (Int, Int) [Token]
runHolLexer src = do
    case unterminatedBlockComment src of
        Just start -> Left start
        Nothing -> return ()
    tokens <- runHolLexerRaw src
    case [start | T_lex_error (SLoc start _) <- tokens] of
        start : _ -> Left start
        [] -> Right tokens

-- Keep the hand-written lexical policy in sync with the generated DFA.  The
-- DFA recognizes complete, non-nesting `(* ... *)' comments; this preflight
-- prevents an unterminated opener from falling back to ordinary punctuation.
unterminatedBlockComment :: String -> Maybe (Int, Int)
unterminatedBlockComment = normal 1 1 where
    normal _ _ [] = Nothing
    normal row col ('(' : '*' : rest) = block (row, col) row (col + 2) rest
    normal row col ('%' : rest) = lineComment row (col + 1) rest
    normal row col ('"' : rest) = quoted '"' row (col + 1) rest
    normal row col ('\'' : rest) = quoted '\'' row (col + 1) rest
    normal row col input@(ch : _)
        | isSymbolStart ch =
            let ((row', col'), rest) = consumeSymbol row col input
            in normal row' col' rest
    normal row col (ch : rest) = uncurry normal (advance row col ch) rest

    lineComment _ _ [] = Nothing
    lineComment row col ('\n' : rest) = normal (row + 1) 1 rest
    lineComment row col (_ : rest) = lineComment row (col + 1) rest

    quoted _ _ _ [] = Nothing
    quoted quote row col ('\\' : escaped : rest) =
        let (row', col') = advance row col '\\'
            (row'', col'') = advance row' col' escaped
        in quoted quote row'' col'' rest
    quoted quote row col (ch : rest)
        | ch == quote = uncurry normal (advance row col ch) rest
        | otherwise = uncurry (quoted quote) (advance row col ch) rest

    block start _ _ [] = Just start
    block _ row col ('*' : ')' : rest) = normal row (col + 2) rest
    block start row col (ch : rest) = uncurry (block start) (advance row col ch) rest

    consumeSymbol row col [] = ((row, col), [])
    consumeSymbol row col input@(ch : rest)
        | isSymbolRest ch =
            let (row', col') = advance row col ch
            in consumeSymbol row' col' rest
        | otherwise = ((row, col), input)

    isSymbolStart ch = ch `elem` ("!@#$^&*+-=<>?/|~:" :: String)
    isSymbolRest ch = isSymbolStart ch || ch == '%'
    advance row _ '\n' = (row + 1, 1)
    advance row col _ = (row, col + 1)

isHolLiteralChar :: Char -> Bool
isHolLiteralChar ch = isPrint ch || ch == '\n' || ch == '\t'

isHolEscapeCode :: Char -> Bool
isHolEscapeCode ch = ch `elem` ['n', 't', '\\', '\"', '\'']

validHolStringLexeme :: String -> Bool
validHolStringLexeme ('\"' : rest) = scan rest where
    scan ['\"'] = True
    scan ('\\' : escaped : more)
        | isHolEscapeCode escaped = scan more
    scan (ch : more)
        | isPrint ch && ch /= '\"' && ch /= '\\' = scan more
    scan _ = False
validHolStringLexeme _ = False

validHolCharLexeme :: String -> Bool
validHolCharLexeme ['\'', '\\', escaped, '\''] = isHolEscapeCode escaped
validHolCharLexeme ['\'', ch, '\''] = isPrint ch && ch /= '\'' && ch /= '\\'
validHolCharLexeme _ = False

readHolStringLiteral :: String -> Maybe String
readHolStringLiteral src
    | validHolStringLexeme src = case reads src of
        [(str, "")] | all isHolLiteralChar str -> Just str
        _ -> Nothing
    | otherwise = Nothing

readHolCharLiteral :: String -> Maybe Char
readHolCharLiteral src
    | validHolCharLexeme src = case reads src of
        [(ch, "")] | isHolLiteralChar ch -> Just ch
        _ -> Nothing
    | otherwise = Nothing

mkStringToken :: SLoc -> String -> Token
mkStringToken loc src = maybe (T_lex_error loc) (T_str_lit loc) (readHolStringLiteral src)

mkCharToken :: SLoc -> String -> Token
mkCharToken loc src = maybe (T_lex_error loc) (T_chr_lit loc) (readHolCharLiteral src)

mkStrLit :: SLoc -> String -> TermRep
mkStrLit loc str = foldr (\ch -> \acc -> RApp loc (RApp loc (RCon loc DC_Cons) (RCon loc (DC_ChrL ch))) acc) (RCon loc DC_Nil) str

-- the following codes are generated by LGS.

data DFA
    = DFA
        { getInitialQOfDFA :: Int
        , getFinalQsOfDFA :: XMap.Map Int Int
        , getTransitionsOfDFA :: XMap.Map (Int, Maybe Char) Int
        }
    deriving ()

runHolLexerRaw :: String -> Either (Int, Int) [Token]
runHolLexerRaw = runHolLexerRaw_this . addLoc 1 1 where
    theDFA :: DFA
    theDFA = DFA
        { getInitialQOfDFA = 12
        , getFinalQsOfDFA = XMap.fromAscList [(13, 1), (14, 2), (15, 3), (16, 4), (17, 5), (18, 6), (19, 7), (20, 8), (21, 9), (22, 10), (23, 12), (24, 13), (25, 14), (26, 15), (27, 16), (28, 17), (29, 18), (30, 19), (31, 20), (32, 21), (33, 22), (34, 23), (35, 24), (36, 25), (37, 26), (38, 27), (39, 28), (40, 29), (41, 30), (42, 31), (43, 32), (44, 33), (45, 34), (46, 35), (47, 36), (48, 36), (49, 36), (50, 36), (51, 36), (52, 36), (53, 36), (54, 36), (55, 36), (56, 36), (57, 36), (58, 36), (59, 36), (60, 36), (61, 36), (62, 36), (63, 36), (64, 36), (65, 36), (66, 36), (67, 36), (68, 37), (69, 38), (70, 39), (71, 40), (72, 41), (73, 42)]
        , getTransitionsOfDFA = XMap.fromList
            [ ((0, Just '"'), 6), ((0, Just '\''), 6), ((0, Just '\\'), 6), ((0, Just 'n'), 6), ((0, Just 't'), 6)
            , ((1, Just '\t'), 7), ((1, Just '\r'), 7), ((1, Just ' '), 7), ((1, Just '!'), 7), ((1, Just '"'), 7), ((1, Just '%'), 7), ((1, Just '('), 7), ((1, Just ')'), 7), ((1, Just '*'), 7), ((1, Just '+'), 7), ((1, Just ','), 7), ((1, Just '-'), 7), ((1, Just '.'), 7), ((1, Just '/'), 7), ((1, Just '0'), 7), ((1, Just '1'), 7), ((1, Just '2'), 7), ((1, Just '3'), 7), ((1, Just '4'), 7), ((1, Just '5'), 7), ((1, Just '6'), 7), ((1, Just '7'), 7), ((1, Just '8'), 7), ((1, Just '9'), 7), ((1, Just ':'), 7), ((1, Just ';'), 7), ((1, Just '<'), 7), ((1, Just '='), 7), ((1, Just '>'), 7), ((1, Just '?'), 7), ((1, Just 'A'), 7), ((1, Just 'B'), 7), ((1, Just 'C'), 7), ((1, Just 'D'), 7), ((1, Just 'E'), 7), ((1, Just 'F'), 7), ((1, Just 'G'), 7), ((1, Just 'H'), 7), ((1, Just 'I'), 7), ((1, Just 'J'), 7), ((1, Just 'K'), 7), ((1, Just 'L'), 7), ((1, Just 'M'), 7), ((1, Just 'N'), 7), ((1, Just 'O'), 7), ((1, Just 'P'), 7), ((1, Just 'Q'), 7), ((1, Just 'R'), 7), ((1, Just 'S'), 7), ((1, Just 'T'), 7), ((1, Just 'U'), 7), ((1, Just 'V'), 7), ((1, Just 'W'), 7), ((1, Just 'X'), 7), ((1, Just 'Y'), 7), ((1, Just 'Z'), 7), ((1, Just '['), 7), ((1, Just '\\'), 2), ((1, Just ']'), 7), ((1, Just '_'), 7), ((1, Just '`'), 7), ((1, Just 'a'), 7), ((1, Just 'b'), 7), ((1, Just 'c'), 7), ((1, Just 'd'), 7), ((1, Just 'e'), 7), ((1, Just 'f'), 7), ((1, Just 'g'), 7), ((1, Just 'h'), 7), ((1, Just 'i'), 7), ((1, Just 'j'), 7), ((1, Just 'k'), 7), ((1, Just 'l'), 7), ((1, Just 'm'), 7), ((1, Just 'n'), 7), ((1, Just 'o'), 7), ((1, Just 'p'), 7), ((1, Just 'q'), 7), ((1, Just 'r'), 7), ((1, Just 's'), 7), ((1, Just 't'), 7), ((1, Just 'u'), 7), ((1, Just 'v'), 7), ((1, Just 'w'), 7), ((1, Just 'x'), 7), ((1, Just 'y'), 7), ((1, Just 'z'), 7), ((1, Nothing), 7)
            , ((2, Just '"'), 7), ((2, Just '\''), 7), ((2, Just '\\'), 7), ((2, Just 'n'), 7), ((2, Just 't'), 7)
            , ((3, Just '\t'), 3), ((3, Just '\n'), 3), ((3, Just '\r'), 3), ((3, Just ' '), 3), ((3, Just '!'), 3), ((3, Just '"'), 3), ((3, Just '%'), 3), ((3, Just '\''), 3), ((3, Just '('), 3), ((3, Just ')'), 3), ((3, Just '*'), 8), ((3, Just '+'), 3), ((3, Just ','), 3), ((3, Just '-'), 3), ((3, Just '.'), 3), ((3, Just '/'), 3), ((3, Just '0'), 3), ((3, Just '1'), 3), ((3, Just '2'), 3), ((3, Just '3'), 3), ((3, Just '4'), 3), ((3, Just '5'), 3), ((3, Just '6'), 3), ((3, Just '7'), 3), ((3, Just '8'), 3), ((3, Just '9'), 3), ((3, Just ':'), 3), ((3, Just ';'), 3), ((3, Just '<'), 3), ((3, Just '='), 3), ((3, Just '>'), 3), ((3, Just '?'), 3), ((3, Just 'A'), 3), ((3, Just 'B'), 3), ((3, Just 'C'), 3), ((3, Just 'D'), 3), ((3, Just 'E'), 3), ((3, Just 'F'), 3), ((3, Just 'G'), 3), ((3, Just 'H'), 3), ((3, Just 'I'), 3), ((3, Just 'J'), 3), ((3, Just 'K'), 3), ((3, Just 'L'), 3), ((3, Just 'M'), 3), ((3, Just 'N'), 3), ((3, Just 'O'), 3), ((3, Just 'P'), 3), ((3, Just 'Q'), 3), ((3, Just 'R'), 3), ((3, Just 'S'), 3), ((3, Just 'T'), 3), ((3, Just 'U'), 3), ((3, Just 'V'), 3), ((3, Just 'W'), 3), ((3, Just 'X'), 3), ((3, Just 'Y'), 3), ((3, Just 'Z'), 3), ((3, Just '['), 3), ((3, Just '\\'), 3), ((3, Just ']'), 3), ((3, Just '_'), 3), ((3, Just '`'), 3), ((3, Just 'a'), 3), ((3, Just 'b'), 3), ((3, Just 'c'), 3), ((3, Just 'd'), 3), ((3, Just 'e'), 3), ((3, Just 'f'), 3), ((3, Just 'g'), 3), ((3, Just 'h'), 3), ((3, Just 'i'), 3), ((3, Just 'j'), 3), ((3, Just 'k'), 3), ((3, Just 'l'), 3), ((3, Just 'm'), 3), ((3, Just 'n'), 3), ((3, Just 'o'), 3), ((3, Just 'p'), 3), ((3, Just 'q'), 3), ((3, Just 'r'), 3), ((3, Just 's'), 3), ((3, Just 't'), 3), ((3, Just 'u'), 3), ((3, Just 'v'), 3), ((3, Just 'w'), 3), ((3, Just 'x'), 3), ((3, Just 'y'), 3), ((3, Just 'z'), 3), ((3, Nothing), 3)
            , ((5, Just 'a'), 11), ((5, Just 'b'), 11), ((5, Just 'c'), 11), ((5, Just 'd'), 11), ((5, Just 'e'), 11), ((5, Just 'f'), 11), ((5, Just 'g'), 11), ((5, Just 'h'), 11), ((5, Just 'i'), 11), ((5, Just 'j'), 11), ((5, Just 'k'), 11), ((5, Just 'l'), 11), ((5, Just 'm'), 11), ((5, Just 'n'), 11), ((5, Just 'o'), 11), ((5, Just 'p'), 11), ((5, Just 'q'), 11), ((5, Just 'r'), 11), ((5, Just 's'), 11), ((5, Just 't'), 11), ((5, Just 'u'), 11), ((5, Just 'v'), 11), ((5, Just 'w'), 11), ((5, Just 'x'), 11), ((5, Just 'y'), 11), ((5, Just 'z'), 11)
            , ((6, Just '\t'), 6), ((6, Just '\r'), 6), ((6, Just ' '), 6), ((6, Just '!'), 6), ((6, Just '"'), 69), ((6, Just '%'), 6), ((6, Just '\''), 6), ((6, Just '('), 6), ((6, Just ')'), 6), ((6, Just '*'), 6), ((6, Just '+'), 6), ((6, Just ','), 6), ((6, Just '-'), 6), ((6, Just '.'), 6), ((6, Just '/'), 6), ((6, Just '0'), 6), ((6, Just '1'), 6), ((6, Just '2'), 6), ((6, Just '3'), 6), ((6, Just '4'), 6), ((6, Just '5'), 6), ((6, Just '6'), 6), ((6, Just '7'), 6), ((6, Just '8'), 6), ((6, Just '9'), 6), ((6, Just ':'), 6), ((6, Just ';'), 6), ((6, Just '<'), 6), ((6, Just '='), 6), ((6, Just '>'), 6), ((6, Just '?'), 6), ((6, Just 'A'), 6), ((6, Just 'B'), 6), ((6, Just 'C'), 6), ((6, Just 'D'), 6), ((6, Just 'E'), 6), ((6, Just 'F'), 6), ((6, Just 'G'), 6), ((6, Just 'H'), 6), ((6, Just 'I'), 6), ((6, Just 'J'), 6), ((6, Just 'K'), 6), ((6, Just 'L'), 6), ((6, Just 'M'), 6), ((6, Just 'N'), 6), ((6, Just 'O'), 6), ((6, Just 'P'), 6), ((6, Just 'Q'), 6), ((6, Just 'R'), 6), ((6, Just 'S'), 6), ((6, Just 'T'), 6), ((6, Just 'U'), 6), ((6, Just 'V'), 6), ((6, Just 'W'), 6), ((6, Just 'X'), 6), ((6, Just 'Y'), 6), ((6, Just 'Z'), 6), ((6, Just '['), 6), ((6, Just '\\'), 0), ((6, Just ']'), 6), ((6, Just '_'), 6), ((6, Just '`'), 6), ((6, Just 'a'), 6), ((6, Just 'b'), 6), ((6, Just 'c'), 6), ((6, Just 'd'), 6), ((6, Just 'e'), 6), ((6, Just 'f'), 6), ((6, Just 'g'), 6), ((6, Just 'h'), 6), ((6, Just 'i'), 6), ((6, Just 'j'), 6), ((6, Just 'k'), 6), ((6, Just 'l'), 6), ((6, Just 'm'), 6), ((6, Just 'n'), 6), ((6, Just 'o'), 6), ((6, Just 'p'), 6), ((6, Just 'q'), 6), ((6, Just 'r'), 6), ((6, Just 's'), 6), ((6, Just 't'), 6), ((6, Just 'u'), 6), ((6, Just 'v'), 6), ((6, Just 'w'), 6), ((6, Just 'x'), 6), ((6, Just 'y'), 6), ((6, Just 'z'), 6), ((6, Nothing), 6)
            , ((7, Just '\''), 70)
            , ((8, Just '\t'), 3), ((8, Just '\n'), 3), ((8, Just '\r'), 3), ((8, Just ' '), 3), ((8, Just '!'), 3), ((8, Just '"'), 3), ((8, Just '%'), 3), ((8, Just '\''), 3), ((8, Just '('), 3), ((8, Just ')'), 73), ((8, Just '*'), 3), ((8, Just '+'), 3), ((8, Just ','), 3), ((8, Just '-'), 3), ((8, Just '.'), 3), ((8, Just '/'), 3), ((8, Just '0'), 3), ((8, Just '1'), 3), ((8, Just '2'), 3), ((8, Just '3'), 3), ((8, Just '4'), 3), ((8, Just '5'), 3), ((8, Just '6'), 3), ((8, Just '7'), 3), ((8, Just '8'), 3), ((8, Just '9'), 3), ((8, Just ':'), 3), ((8, Just ';'), 3), ((8, Just '<'), 3), ((8, Just '='), 3), ((8, Just '>'), 3), ((8, Just '?'), 3), ((8, Just 'A'), 3), ((8, Just 'B'), 3), ((8, Just 'C'), 3), ((8, Just 'D'), 3), ((8, Just 'E'), 3), ((8, Just 'F'), 3), ((8, Just 'G'), 3), ((8, Just 'H'), 3), ((8, Just 'I'), 3), ((8, Just 'J'), 3), ((8, Just 'K'), 3), ((8, Just 'L'), 3), ((8, Just 'M'), 3), ((8, Just 'N'), 3), ((8, Just 'O'), 3), ((8, Just 'P'), 3), ((8, Just 'Q'), 3), ((8, Just 'R'), 3), ((8, Just 'S'), 3), ((8, Just 'T'), 3), ((8, Just 'U'), 3), ((8, Just 'V'), 3), ((8, Just 'W'), 3), ((8, Just 'X'), 3), ((8, Just 'Y'), 3), ((8, Just 'Z'), 3), ((8, Just '['), 3), ((8, Just '\\'), 3), ((8, Just ']'), 3), ((8, Just '_'), 3), ((8, Just '`'), 3), ((8, Just 'a'), 3), ((8, Just 'b'), 3), ((8, Just 'c'), 3), ((8, Just 'd'), 3), ((8, Just 'e'), 3), ((8, Just 'f'), 3), ((8, Just 'g'), 3), ((8, Just 'h'), 3), ((8, Just 'i'), 3), ((8, Just 'j'), 3), ((8, Just 'k'), 3), ((8, Just 'l'), 3), ((8, Just 'm'), 3), ((8, Just 'n'), 3), ((8, Just 'o'), 3), ((8, Just 'p'), 3), ((8, Just 'q'), 3), ((8, Just 'r'), 3), ((8, Just 's'), 3), ((8, Just 't'), 3), ((8, Just 'u'), 3), ((8, Just 'v'), 3), ((8, Just 'w'), 3), ((8, Just 'x'), 3), ((8, Just 'y'), 3), ((8, Just 'z'), 3), ((8, Nothing), 3)
            , ((9, Just '-'), 21)
            , ((10, Just '-'), 23), ((10, Just ':'), 43)
            , ((11, Just '0'), 11), ((11, Just '1'), 11), ((11, Just '2'), 11), ((11, Just '3'), 11), ((11, Just '4'), 11), ((11, Just '5'), 11), ((11, Just '6'), 11), ((11, Just '7'), 11), ((11, Just '8'), 11), ((11, Just '9'), 11), ((11, Just 'A'), 11), ((11, Just 'B'), 11), ((11, Just 'C'), 11), ((11, Just 'D'), 11), ((11, Just 'E'), 11), ((11, Just 'F'), 11), ((11, Just 'G'), 11), ((11, Just 'H'), 11), ((11, Just 'I'), 11), ((11, Just 'J'), 11), ((11, Just 'K'), 11), ((11, Just 'L'), 11), ((11, Just 'M'), 11), ((11, Just 'N'), 11), ((11, Just 'O'), 11), ((11, Just 'P'), 11), ((11, Just 'Q'), 11), ((11, Just 'R'), 11), ((11, Just 'S'), 11), ((11, Just 'T'), 11), ((11, Just 'U'), 11), ((11, Just 'V'), 11), ((11, Just 'W'), 11), ((11, Just 'X'), 11), ((11, Just 'Y'), 11), ((11, Just 'Z'), 11), ((11, Just '_'), 11), ((11, Just '`'), 46), ((11, Just 'a'), 11), ((11, Just 'b'), 11), ((11, Just 'c'), 11), ((11, Just 'd'), 11), ((11, Just 'e'), 11), ((11, Just 'f'), 11), ((11, Just 'g'), 11), ((11, Just 'h'), 11), ((11, Just 'i'), 11), ((11, Just 'j'), 11), ((11, Just 'k'), 11), ((11, Just 'l'), 11), ((11, Just 'm'), 11), ((11, Just 'n'), 11), ((11, Just 'o'), 11), ((11, Just 'p'), 11), ((11, Just 'q'), 11), ((11, Just 'r'), 11), ((11, Just 's'), 11), ((11, Just 't'), 11), ((11, Just 'u'), 11), ((11, Just 'v'), 11), ((11, Just 'w'), 11), ((11, Just 'x'), 11), ((11, Just 'y'), 11), ((11, Just 'z'), 11)
            , ((12, Just '\t'), 71), ((12, Just '\n'), 71), ((12, Just '\r'), 71), ((12, Just ' '), 71), ((12, Just '!'), 37), ((12, Just '"'), 6), ((12, Just '%'), 72), ((12, Just '\''), 1), ((12, Just '('), 17), ((12, Just ')'), 18), ((12, Just '*'), 32), ((12, Just '+'), 30), ((12, Just ','), 22), ((12, Just '-'), 31), ((12, Just '.'), 14), ((12, Just '/'), 33), ((12, Just '0'), 68), ((12, Just '1'), 68), ((12, Just '2'), 68), ((12, Just '3'), 68), ((12, Just '4'), 68), ((12, Just '5'), 68), ((12, Just '6'), 68), ((12, Just '7'), 68), ((12, Just '8'), 68), ((12, Just '9'), 68), ((12, Just ':'), 10), ((12, Just ';'), 36), ((12, Just '<'), 27), ((12, Just '='), 25), ((12, Just '>'), 29), ((12, Just '?'), 9), ((12, Just 'A'), 60), ((12, Just 'B'), 60), ((12, Just 'C'), 60), ((12, Just 'D'), 60), ((12, Just 'E'), 60), ((12, Just 'F'), 60), ((12, Just 'G'), 60), ((12, Just 'H'), 60), ((12, Just 'I'), 60), ((12, Just 'J'), 60), ((12, Just 'K'), 60), ((12, Just 'L'), 60), ((12, Just 'M'), 60), ((12, Just 'N'), 60), ((12, Just 'O'), 60), ((12, Just 'P'), 60), ((12, Just 'Q'), 60), ((12, Just 'R'), 60), ((12, Just 'S'), 60), ((12, Just 'T'), 60), ((12, Just 'U'), 60), ((12, Just 'V'), 60), ((12, Just 'W'), 60), ((12, Just 'X'), 60), ((12, Just 'Y'), 60), ((12, Just 'Z'), 60), ((12, Just '['), 19), ((12, Just '\\'), 42), ((12, Just ']'), 20), ((12, Just '_'), 13), ((12, Just '`'), 5), ((12, Just 'a'), 60), ((12, Just 'b'), 60), ((12, Just 'c'), 60), ((12, Just 'd'), 57), ((12, Just 'e'), 60), ((12, Just 'f'), 59), ((12, Just 'g'), 60), ((12, Just 'h'), 60), ((12, Just 'i'), 67), ((12, Just 'j'), 60), ((12, Just 'k'), 51), ((12, Just 'l'), 60), ((12, Just 'm'), 60), ((12, Just 'n'), 60), ((12, Just 'o'), 60), ((12, Just 'p'), 47), ((12, Just 'q'), 60), ((12, Just 'r'), 60), ((12, Just 's'), 24), ((12, Just 't'), 54), ((12, Just 'u'), 60), ((12, Just 'v'), 60), ((12, Just 'w'), 60), ((12, Just 'x'), 60), ((12, Just 'y'), 60), ((12, Just 'z'), 60)
            , ((17, Just '*'), 3)
            , ((24, Just '0'), 60), ((24, Just '1'), 60), ((24, Just '2'), 60), ((24, Just '3'), 60), ((24, Just '4'), 60), ((24, Just '5'), 60), ((24, Just '6'), 60), ((24, Just '7'), 60), ((24, Just '8'), 60), ((24, Just '9'), 60), ((24, Just 'A'), 60), ((24, Just 'B'), 60), ((24, Just 'C'), 60), ((24, Just 'D'), 60), ((24, Just 'E'), 60), ((24, Just 'F'), 60), ((24, Just 'G'), 60), ((24, Just 'H'), 60), ((24, Just 'I'), 60), ((24, Just 'J'), 60), ((24, Just 'K'), 60), ((24, Just 'L'), 60), ((24, Just 'M'), 60), ((24, Just 'N'), 60), ((24, Just 'O'), 60), ((24, Just 'P'), 60), ((24, Just 'Q'), 60), ((24, Just 'R'), 60), ((24, Just 'S'), 60), ((24, Just 'T'), 60), ((24, Just 'U'), 60), ((24, Just 'V'), 60), ((24, Just 'W'), 60), ((24, Just 'X'), 60), ((24, Just 'Y'), 60), ((24, Just 'Z'), 60), ((24, Just '_'), 60), ((24, Just 'a'), 60), ((24, Just 'b'), 60), ((24, Just 'c'), 60), ((24, Just 'd'), 60), ((24, Just 'e'), 60), ((24, Just 'f'), 60), ((24, Just 'g'), 60), ((24, Just 'h'), 60), ((24, Just 'i'), 49), ((24, Just 'j'), 60), ((24, Just 'k'), 60), ((24, Just 'l'), 60), ((24, Just 'm'), 60), ((24, Just 'n'), 60), ((24, Just 'o'), 60), ((24, Just 'p'), 60), ((24, Just 'q'), 60), ((24, Just 'r'), 60), ((24, Just 's'), 60), ((24, Just 't'), 60), ((24, Just 'u'), 60), ((24, Just 'v'), 60), ((24, Just 'w'), 60), ((24, Just 'x'), 60), ((24, Just 'y'), 60), ((24, Just 'z'), 60)
            , ((25, Just '<'), 26), ((25, Just '>'), 16)
            , ((29, Just '='), 28)
            , ((31, Just '>'), 15)
            , ((34, Just '0'), 60), ((34, Just '1'), 60), ((34, Just '2'), 60), ((34, Just '3'), 60), ((34, Just '4'), 60), ((34, Just '5'), 60), ((34, Just '6'), 60), ((34, Just '7'), 60), ((34, Just '8'), 60), ((34, Just '9'), 60), ((34, Just 'A'), 60), ((34, Just 'B'), 60), ((34, Just 'C'), 60), ((34, Just 'D'), 60), ((34, Just 'E'), 60), ((34, Just 'F'), 60), ((34, Just 'G'), 60), ((34, Just 'H'), 60), ((34, Just 'I'), 60), ((34, Just 'J'), 60), ((34, Just 'K'), 60), ((34, Just 'L'), 60), ((34, Just 'M'), 60), ((34, Just 'N'), 60), ((34, Just 'O'), 60), ((34, Just 'P'), 60), ((34, Just 'Q'), 60), ((34, Just 'R'), 60), ((34, Just 'S'), 60), ((34, Just 'T'), 60), ((34, Just 'U'), 60), ((34, Just 'V'), 60), ((34, Just 'W'), 60), ((34, Just 'X'), 60), ((34, Just 'Y'), 60), ((34, Just 'Z'), 60), ((34, Just '_'), 60), ((34, Just 'a'), 60), ((34, Just 'b'), 60), ((34, Just 'c'), 60), ((34, Just 'd'), 60), ((34, Just 'e'), 60), ((34, Just 'f'), 60), ((34, Just 'g'), 60), ((34, Just 'h'), 60), ((34, Just 'i'), 60), ((34, Just 'j'), 60), ((34, Just 'k'), 60), ((34, Just 'l'), 60), ((34, Just 'm'), 60), ((34, Just 'n'), 60), ((34, Just 'o'), 60), ((34, Just 'p'), 60), ((34, Just 'q'), 60), ((34, Just 'r'), 60), ((34, Just 's'), 60), ((34, Just 't'), 60), ((34, Just 'u'), 60), ((34, Just 'v'), 60), ((34, Just 'w'), 60), ((34, Just 'x'), 60), ((34, Just 'y'), 60), ((34, Just 'z'), 60)
            , ((35, Just '0'), 60), ((35, Just '1'), 60), ((35, Just '2'), 60), ((35, Just '3'), 60), ((35, Just '4'), 60), ((35, Just '5'), 60), ((35, Just '6'), 60), ((35, Just '7'), 60), ((35, Just '8'), 60), ((35, Just '9'), 60), ((35, Just 'A'), 60), ((35, Just 'B'), 60), ((35, Just 'C'), 60), ((35, Just 'D'), 60), ((35, Just 'E'), 60), ((35, Just 'F'), 60), ((35, Just 'G'), 60), ((35, Just 'H'), 60), ((35, Just 'I'), 60), ((35, Just 'J'), 60), ((35, Just 'K'), 60), ((35, Just 'L'), 60), ((35, Just 'M'), 60), ((35, Just 'N'), 60), ((35, Just 'O'), 60), ((35, Just 'P'), 60), ((35, Just 'Q'), 60), ((35, Just 'R'), 60), ((35, Just 'S'), 60), ((35, Just 'T'), 60), ((35, Just 'U'), 60), ((35, Just 'V'), 60), ((35, Just 'W'), 60), ((35, Just 'X'), 60), ((35, Just 'Y'), 60), ((35, Just 'Z'), 60), ((35, Just '_'), 60), ((35, Just 'a'), 60), ((35, Just 'b'), 60), ((35, Just 'c'), 60), ((35, Just 'd'), 60), ((35, Just 'e'), 60), ((35, Just 'f'), 60), ((35, Just 'g'), 60), ((35, Just 'h'), 60), ((35, Just 'i'), 60), ((35, Just 'j'), 60), ((35, Just 'k'), 60), ((35, Just 'l'), 60), ((35, Just 'm'), 60), ((35, Just 'n'), 60), ((35, Just 'o'), 60), ((35, Just 'p'), 60), ((35, Just 'q'), 60), ((35, Just 'r'), 60), ((35, Just 's'), 60), ((35, Just 't'), 60), ((35, Just 'u'), 60), ((35, Just 'v'), 60), ((35, Just 'w'), 60), ((35, Just 'x'), 60), ((35, Just 'y'), 60), ((35, Just 'z'), 60)
            , ((38, Just '0'), 60), ((38, Just '1'), 60), ((38, Just '2'), 60), ((38, Just '3'), 60), ((38, Just '4'), 60), ((38, Just '5'), 60), ((38, Just '6'), 60), ((38, Just '7'), 60), ((38, Just '8'), 60), ((38, Just '9'), 60), ((38, Just 'A'), 60), ((38, Just 'B'), 60), ((38, Just 'C'), 60), ((38, Just 'D'), 60), ((38, Just 'E'), 60), ((38, Just 'F'), 60), ((38, Just 'G'), 60), ((38, Just 'H'), 60), ((38, Just 'I'), 60), ((38, Just 'J'), 60), ((38, Just 'K'), 60), ((38, Just 'L'), 60), ((38, Just 'M'), 60), ((38, Just 'N'), 60), ((38, Just 'O'), 60), ((38, Just 'P'), 60), ((38, Just 'Q'), 60), ((38, Just 'R'), 60), ((38, Just 'S'), 60), ((38, Just 'T'), 60), ((38, Just 'U'), 60), ((38, Just 'V'), 60), ((38, Just 'W'), 60), ((38, Just 'X'), 60), ((38, Just 'Y'), 60), ((38, Just 'Z'), 60), ((38, Just '_'), 60), ((38, Just 'a'), 60), ((38, Just 'b'), 60), ((38, Just 'c'), 60), ((38, Just 'd'), 60), ((38, Just 'e'), 60), ((38, Just 'f'), 60), ((38, Just 'g'), 60), ((38, Just 'h'), 60), ((38, Just 'i'), 60), ((38, Just 'j'), 60), ((38, Just 'k'), 60), ((38, Just 'l'), 60), ((38, Just 'm'), 60), ((38, Just 'n'), 60), ((38, Just 'o'), 60), ((38, Just 'p'), 60), ((38, Just 'q'), 60), ((38, Just 'r'), 60), ((38, Just 's'), 60), ((38, Just 't'), 60), ((38, Just 'u'), 60), ((38, Just 'v'), 60), ((38, Just 'w'), 60), ((38, Just 'x'), 60), ((38, Just 'y'), 60), ((38, Just 'z'), 60)
            , ((39, Just '0'), 60), ((39, Just '1'), 60), ((39, Just '2'), 60), ((39, Just '3'), 60), ((39, Just '4'), 60), ((39, Just '5'), 60), ((39, Just '6'), 60), ((39, Just '7'), 60), ((39, Just '8'), 60), ((39, Just '9'), 60), ((39, Just 'A'), 60), ((39, Just 'B'), 60), ((39, Just 'C'), 60), ((39, Just 'D'), 60), ((39, Just 'E'), 60), ((39, Just 'F'), 60), ((39, Just 'G'), 60), ((39, Just 'H'), 60), ((39, Just 'I'), 60), ((39, Just 'J'), 60), ((39, Just 'K'), 60), ((39, Just 'L'), 60), ((39, Just 'M'), 60), ((39, Just 'N'), 60), ((39, Just 'O'), 60), ((39, Just 'P'), 60), ((39, Just 'Q'), 60), ((39, Just 'R'), 60), ((39, Just 'S'), 60), ((39, Just 'T'), 60), ((39, Just 'U'), 60), ((39, Just 'V'), 60), ((39, Just 'W'), 60), ((39, Just 'X'), 60), ((39, Just 'Y'), 60), ((39, Just 'Z'), 60), ((39, Just '_'), 60), ((39, Just 'a'), 60), ((39, Just 'b'), 60), ((39, Just 'c'), 60), ((39, Just 'd'), 60), ((39, Just 'e'), 60), ((39, Just 'f'), 60), ((39, Just 'g'), 60), ((39, Just 'h'), 60), ((39, Just 'i'), 60), ((39, Just 'j'), 60), ((39, Just 'k'), 60), ((39, Just 'l'), 60), ((39, Just 'm'), 60), ((39, Just 'n'), 60), ((39, Just 'o'), 60), ((39, Just 'p'), 60), ((39, Just 'q'), 60), ((39, Just 'r'), 60), ((39, Just 's'), 60), ((39, Just 't'), 60), ((39, Just 'u'), 60), ((39, Just 'v'), 60), ((39, Just 'w'), 60), ((39, Just 'x'), 60), ((39, Just 'y'), 60), ((39, Just 'z'), 60)
            , ((40, Just '0'), 60), ((40, Just '1'), 60), ((40, Just '2'), 60), ((40, Just '3'), 60), ((40, Just '4'), 60), ((40, Just '5'), 60), ((40, Just '6'), 60), ((40, Just '7'), 60), ((40, Just '8'), 60), ((40, Just '9'), 60), ((40, Just 'A'), 60), ((40, Just 'B'), 60), ((40, Just 'C'), 60), ((40, Just 'D'), 60), ((40, Just 'E'), 60), ((40, Just 'F'), 60), ((40, Just 'G'), 60), ((40, Just 'H'), 60), ((40, Just 'I'), 60), ((40, Just 'J'), 60), ((40, Just 'K'), 60), ((40, Just 'L'), 60), ((40, Just 'M'), 60), ((40, Just 'N'), 60), ((40, Just 'O'), 60), ((40, Just 'P'), 60), ((40, Just 'Q'), 60), ((40, Just 'R'), 60), ((40, Just 'S'), 60), ((40, Just 'T'), 60), ((40, Just 'U'), 60), ((40, Just 'V'), 60), ((40, Just 'W'), 60), ((40, Just 'X'), 60), ((40, Just 'Y'), 60), ((40, Just 'Z'), 60), ((40, Just '_'), 60), ((40, Just 'a'), 60), ((40, Just 'b'), 60), ((40, Just 'c'), 60), ((40, Just 'd'), 60), ((40, Just 'e'), 60), ((40, Just 'f'), 60), ((40, Just 'g'), 60), ((40, Just 'h'), 60), ((40, Just 'i'), 60), ((40, Just 'j'), 60), ((40, Just 'k'), 60), ((40, Just 'l'), 60), ((40, Just 'm'), 60), ((40, Just 'n'), 60), ((40, Just 'o'), 60), ((40, Just 'p'), 60), ((40, Just 'q'), 60), ((40, Just 'r'), 60), ((40, Just 's'), 60), ((40, Just 't'), 60), ((40, Just 'u'), 60), ((40, Just 'v'), 60), ((40, Just 'w'), 60), ((40, Just 'x'), 60), ((40, Just 'y'), 60), ((40, Just 'z'), 60)
            , ((41, Just '0'), 60), ((41, Just '1'), 60), ((41, Just '2'), 60), ((41, Just '3'), 60), ((41, Just '4'), 60), ((41, Just '5'), 60), ((41, Just '6'), 60), ((41, Just '7'), 60), ((41, Just '8'), 60), ((41, Just '9'), 60), ((41, Just 'A'), 60), ((41, Just 'B'), 60), ((41, Just 'C'), 60), ((41, Just 'D'), 60), ((41, Just 'E'), 60), ((41, Just 'F'), 60), ((41, Just 'G'), 60), ((41, Just 'H'), 60), ((41, Just 'I'), 60), ((41, Just 'J'), 60), ((41, Just 'K'), 60), ((41, Just 'L'), 60), ((41, Just 'M'), 60), ((41, Just 'N'), 60), ((41, Just 'O'), 60), ((41, Just 'P'), 60), ((41, Just 'Q'), 60), ((41, Just 'R'), 60), ((41, Just 'S'), 60), ((41, Just 'T'), 60), ((41, Just 'U'), 60), ((41, Just 'V'), 60), ((41, Just 'W'), 60), ((41, Just 'X'), 60), ((41, Just 'Y'), 60), ((41, Just 'Z'), 60), ((41, Just '_'), 60), ((41, Just 'a'), 60), ((41, Just 'b'), 60), ((41, Just 'c'), 60), ((41, Just 'd'), 60), ((41, Just 'e'), 60), ((41, Just 'f'), 60), ((41, Just 'g'), 60), ((41, Just 'h'), 60), ((41, Just 'i'), 60), ((41, Just 'j'), 60), ((41, Just 'k'), 60), ((41, Just 'l'), 60), ((41, Just 'm'), 60), ((41, Just 'n'), 60), ((41, Just 'o'), 60), ((41, Just 'p'), 60), ((41, Just 'q'), 60), ((41, Just 'r'), 60), ((41, Just 's'), 60), ((41, Just 't'), 60), ((41, Just 'u'), 60), ((41, Just 'v'), 60), ((41, Just 'w'), 60), ((41, Just 'x'), 60), ((41, Just 'y'), 60), ((41, Just 'z'), 60)
            , ((44, Just '0'), 60), ((44, Just '1'), 60), ((44, Just '2'), 60), ((44, Just '3'), 60), ((44, Just '4'), 60), ((44, Just '5'), 60), ((44, Just '6'), 60), ((44, Just '7'), 60), ((44, Just '8'), 60), ((44, Just '9'), 60), ((44, Just 'A'), 60), ((44, Just 'B'), 60), ((44, Just 'C'), 60), ((44, Just 'D'), 60), ((44, Just 'E'), 60), ((44, Just 'F'), 60), ((44, Just 'G'), 60), ((44, Just 'H'), 60), ((44, Just 'I'), 60), ((44, Just 'J'), 60), ((44, Just 'K'), 60), ((44, Just 'L'), 60), ((44, Just 'M'), 60), ((44, Just 'N'), 60), ((44, Just 'O'), 60), ((44, Just 'P'), 60), ((44, Just 'Q'), 60), ((44, Just 'R'), 60), ((44, Just 'S'), 60), ((44, Just 'T'), 60), ((44, Just 'U'), 60), ((44, Just 'V'), 60), ((44, Just 'W'), 60), ((44, Just 'X'), 60), ((44, Just 'Y'), 60), ((44, Just 'Z'), 60), ((44, Just '_'), 60), ((44, Just 'a'), 60), ((44, Just 'b'), 60), ((44, Just 'c'), 60), ((44, Just 'd'), 60), ((44, Just 'e'), 60), ((44, Just 'f'), 60), ((44, Just 'g'), 60), ((44, Just 'h'), 60), ((44, Just 'i'), 60), ((44, Just 'j'), 60), ((44, Just 'k'), 60), ((44, Just 'l'), 60), ((44, Just 'm'), 60), ((44, Just 'n'), 60), ((44, Just 'o'), 60), ((44, Just 'p'), 60), ((44, Just 'q'), 60), ((44, Just 'r'), 60), ((44, Just 's'), 60), ((44, Just 't'), 60), ((44, Just 'u'), 60), ((44, Just 'v'), 60), ((44, Just 'w'), 60), ((44, Just 'x'), 60), ((44, Just 'y'), 60), ((44, Just 'z'), 60)
            , ((45, Just '0'), 60), ((45, Just '1'), 60), ((45, Just '2'), 60), ((45, Just '3'), 60), ((45, Just '4'), 60), ((45, Just '5'), 60), ((45, Just '6'), 60), ((45, Just '7'), 60), ((45, Just '8'), 60), ((45, Just '9'), 60), ((45, Just 'A'), 60), ((45, Just 'B'), 60), ((45, Just 'C'), 60), ((45, Just 'D'), 60), ((45, Just 'E'), 60), ((45, Just 'F'), 60), ((45, Just 'G'), 60), ((45, Just 'H'), 60), ((45, Just 'I'), 60), ((45, Just 'J'), 60), ((45, Just 'K'), 60), ((45, Just 'L'), 60), ((45, Just 'M'), 60), ((45, Just 'N'), 60), ((45, Just 'O'), 60), ((45, Just 'P'), 60), ((45, Just 'Q'), 60), ((45, Just 'R'), 60), ((45, Just 'S'), 60), ((45, Just 'T'), 60), ((45, Just 'U'), 60), ((45, Just 'V'), 60), ((45, Just 'W'), 60), ((45, Just 'X'), 60), ((45, Just 'Y'), 60), ((45, Just 'Z'), 60), ((45, Just '_'), 60), ((45, Just 'a'), 60), ((45, Just 'b'), 60), ((45, Just 'c'), 60), ((45, Just 'd'), 60), ((45, Just 'e'), 60), ((45, Just 'f'), 60), ((45, Just 'g'), 60), ((45, Just 'h'), 60), ((45, Just 'i'), 60), ((45, Just 'j'), 60), ((45, Just 'k'), 60), ((45, Just 'l'), 60), ((45, Just 'm'), 60), ((45, Just 'n'), 60), ((45, Just 'o'), 60), ((45, Just 'p'), 60), ((45, Just 'q'), 60), ((45, Just 'r'), 60), ((45, Just 's'), 60), ((45, Just 't'), 60), ((45, Just 'u'), 60), ((45, Just 'v'), 60), ((45, Just 'w'), 60), ((45, Just 'x'), 60), ((45, Just 'y'), 60), ((45, Just 'z'), 60)
            , ((47, Just '0'), 60), ((47, Just '1'), 60), ((47, Just '2'), 60), ((47, Just '3'), 60), ((47, Just '4'), 60), ((47, Just '5'), 60), ((47, Just '6'), 60), ((47, Just '7'), 60), ((47, Just '8'), 60), ((47, Just '9'), 60), ((47, Just 'A'), 60), ((47, Just 'B'), 60), ((47, Just 'C'), 60), ((47, Just 'D'), 60), ((47, Just 'E'), 60), ((47, Just 'F'), 60), ((47, Just 'G'), 60), ((47, Just 'H'), 60), ((47, Just 'I'), 60), ((47, Just 'J'), 60), ((47, Just 'K'), 60), ((47, Just 'L'), 60), ((47, Just 'M'), 60), ((47, Just 'N'), 60), ((47, Just 'O'), 60), ((47, Just 'P'), 60), ((47, Just 'Q'), 60), ((47, Just 'R'), 60), ((47, Just 'S'), 60), ((47, Just 'T'), 60), ((47, Just 'U'), 60), ((47, Just 'V'), 60), ((47, Just 'W'), 60), ((47, Just 'X'), 60), ((47, Just 'Y'), 60), ((47, Just 'Z'), 60), ((47, Just '_'), 60), ((47, Just 'a'), 60), ((47, Just 'b'), 60), ((47, Just 'c'), 60), ((47, Just 'd'), 60), ((47, Just 'e'), 60), ((47, Just 'f'), 60), ((47, Just 'g'), 60), ((47, Just 'h'), 60), ((47, Just 'i'), 34), ((47, Just 'j'), 60), ((47, Just 'k'), 60), ((47, Just 'l'), 60), ((47, Just 'm'), 60), ((47, Just 'n'), 60), ((47, Just 'o'), 60), ((47, Just 'p'), 60), ((47, Just 'q'), 60), ((47, Just 'r'), 60), ((47, Just 's'), 60), ((47, Just 't'), 60), ((47, Just 'u'), 60), ((47, Just 'v'), 60), ((47, Just 'w'), 60), ((47, Just 'x'), 60), ((47, Just 'y'), 60), ((47, Just 'z'), 60)
            , ((48, Just '0'), 60), ((48, Just '1'), 60), ((48, Just '2'), 60), ((48, Just '3'), 60), ((48, Just '4'), 60), ((48, Just '5'), 60), ((48, Just '6'), 60), ((48, Just '7'), 60), ((48, Just '8'), 60), ((48, Just '9'), 60), ((48, Just 'A'), 60), ((48, Just 'B'), 60), ((48, Just 'C'), 60), ((48, Just 'D'), 60), ((48, Just 'E'), 60), ((48, Just 'F'), 60), ((48, Just 'G'), 60), ((48, Just 'H'), 60), ((48, Just 'I'), 60), ((48, Just 'J'), 60), ((48, Just 'K'), 60), ((48, Just 'L'), 60), ((48, Just 'M'), 60), ((48, Just 'N'), 60), ((48, Just 'O'), 60), ((48, Just 'P'), 60), ((48, Just 'Q'), 60), ((48, Just 'R'), 60), ((48, Just 'S'), 60), ((48, Just 'T'), 60), ((48, Just 'U'), 60), ((48, Just 'V'), 60), ((48, Just 'W'), 60), ((48, Just 'X'), 60), ((48, Just 'Y'), 60), ((48, Just 'Z'), 60), ((48, Just '_'), 60), ((48, Just 'a'), 60), ((48, Just 'b'), 60), ((48, Just 'c'), 60), ((48, Just 'd'), 60), ((48, Just 'e'), 60), ((48, Just 'f'), 60), ((48, Just 'g'), 60), ((48, Just 'h'), 60), ((48, Just 'i'), 60), ((48, Just 'j'), 60), ((48, Just 'k'), 60), ((48, Just 'l'), 60), ((48, Just 'm'), 61), ((48, Just 'n'), 60), ((48, Just 'o'), 60), ((48, Just 'p'), 60), ((48, Just 'q'), 60), ((48, Just 'r'), 60), ((48, Just 's'), 60), ((48, Just 't'), 60), ((48, Just 'u'), 60), ((48, Just 'v'), 60), ((48, Just 'w'), 60), ((48, Just 'x'), 60), ((48, Just 'y'), 60), ((48, Just 'z'), 60)
            , ((49, Just '0'), 60), ((49, Just '1'), 60), ((49, Just '2'), 60), ((49, Just '3'), 60), ((49, Just '4'), 60), ((49, Just '5'), 60), ((49, Just '6'), 60), ((49, Just '7'), 60), ((49, Just '8'), 60), ((49, Just '9'), 60), ((49, Just 'A'), 60), ((49, Just 'B'), 60), ((49, Just 'C'), 60), ((49, Just 'D'), 60), ((49, Just 'E'), 60), ((49, Just 'F'), 60), ((49, Just 'G'), 60), ((49, Just 'H'), 60), ((49, Just 'I'), 60), ((49, Just 'J'), 60), ((49, Just 'K'), 60), ((49, Just 'L'), 60), ((49, Just 'M'), 60), ((49, Just 'N'), 60), ((49, Just 'O'), 60), ((49, Just 'P'), 60), ((49, Just 'Q'), 60), ((49, Just 'R'), 60), ((49, Just 'S'), 60), ((49, Just 'T'), 60), ((49, Just 'U'), 60), ((49, Just 'V'), 60), ((49, Just 'W'), 60), ((49, Just 'X'), 60), ((49, Just 'Y'), 60), ((49, Just 'Z'), 60), ((49, Just '_'), 60), ((49, Just 'a'), 60), ((49, Just 'b'), 60), ((49, Just 'c'), 60), ((49, Just 'd'), 60), ((49, Just 'e'), 60), ((49, Just 'f'), 60), ((49, Just 'g'), 48), ((49, Just 'h'), 60), ((49, Just 'i'), 60), ((49, Just 'j'), 60), ((49, Just 'k'), 60), ((49, Just 'l'), 60), ((49, Just 'm'), 60), ((49, Just 'n'), 60), ((49, Just 'o'), 60), ((49, Just 'p'), 60), ((49, Just 'q'), 60), ((49, Just 'r'), 60), ((49, Just 's'), 60), ((49, Just 't'), 60), ((49, Just 'u'), 60), ((49, Just 'v'), 60), ((49, Just 'w'), 60), ((49, Just 'x'), 60), ((49, Just 'y'), 60), ((49, Just 'z'), 60)
            , ((50, Just '0'), 60), ((50, Just '1'), 60), ((50, Just '2'), 60), ((50, Just '3'), 60), ((50, Just '4'), 60), ((50, Just '5'), 60), ((50, Just '6'), 60), ((50, Just '7'), 60), ((50, Just '8'), 60), ((50, Just '9'), 60), ((50, Just 'A'), 60), ((50, Just 'B'), 60), ((50, Just 'C'), 60), ((50, Just 'D'), 60), ((50, Just 'E'), 60), ((50, Just 'F'), 60), ((50, Just 'G'), 60), ((50, Just 'H'), 60), ((50, Just 'I'), 60), ((50, Just 'J'), 60), ((50, Just 'K'), 60), ((50, Just 'L'), 60), ((50, Just 'M'), 60), ((50, Just 'N'), 60), ((50, Just 'O'), 60), ((50, Just 'P'), 60), ((50, Just 'Q'), 60), ((50, Just 'R'), 60), ((50, Just 'S'), 60), ((50, Just 'T'), 60), ((50, Just 'U'), 60), ((50, Just 'V'), 60), ((50, Just 'W'), 60), ((50, Just 'X'), 60), ((50, Just 'Y'), 60), ((50, Just 'Z'), 60), ((50, Just '_'), 60), ((50, Just 'a'), 60), ((50, Just 'b'), 60), ((50, Just 'c'), 60), ((50, Just 'd'), 60), ((50, Just 'e'), 60), ((50, Just 'f'), 60), ((50, Just 'g'), 60), ((50, Just 'h'), 60), ((50, Just 'i'), 60), ((50, Just 'j'), 60), ((50, Just 'k'), 60), ((50, Just 'l'), 60), ((50, Just 'm'), 60), ((50, Just 'n'), 62), ((50, Just 'o'), 60), ((50, Just 'p'), 60), ((50, Just 'q'), 60), ((50, Just 'r'), 60), ((50, Just 's'), 60), ((50, Just 't'), 60), ((50, Just 'u'), 60), ((50, Just 'v'), 60), ((50, Just 'w'), 60), ((50, Just 'x'), 60), ((50, Just 'y'), 60), ((50, Just 'z'), 60)
            , ((51, Just '0'), 60), ((51, Just '1'), 60), ((51, Just '2'), 60), ((51, Just '3'), 60), ((51, Just '4'), 60), ((51, Just '5'), 60), ((51, Just '6'), 60), ((51, Just '7'), 60), ((51, Just '8'), 60), ((51, Just '9'), 60), ((51, Just 'A'), 60), ((51, Just 'B'), 60), ((51, Just 'C'), 60), ((51, Just 'D'), 60), ((51, Just 'E'), 60), ((51, Just 'F'), 60), ((51, Just 'G'), 60), ((51, Just 'H'), 60), ((51, Just 'I'), 60), ((51, Just 'J'), 60), ((51, Just 'K'), 60), ((51, Just 'L'), 60), ((51, Just 'M'), 60), ((51, Just 'N'), 60), ((51, Just 'O'), 60), ((51, Just 'P'), 60), ((51, Just 'Q'), 60), ((51, Just 'R'), 60), ((51, Just 'S'), 60), ((51, Just 'T'), 60), ((51, Just 'U'), 60), ((51, Just 'V'), 60), ((51, Just 'W'), 60), ((51, Just 'X'), 60), ((51, Just 'Y'), 60), ((51, Just 'Z'), 60), ((51, Just '_'), 60), ((51, Just 'a'), 60), ((51, Just 'b'), 60), ((51, Just 'c'), 60), ((51, Just 'd'), 60), ((51, Just 'e'), 60), ((51, Just 'f'), 60), ((51, Just 'g'), 60), ((51, Just 'h'), 60), ((51, Just 'i'), 50), ((51, Just 'j'), 60), ((51, Just 'k'), 60), ((51, Just 'l'), 60), ((51, Just 'm'), 60), ((51, Just 'n'), 60), ((51, Just 'o'), 60), ((51, Just 'p'), 60), ((51, Just 'q'), 60), ((51, Just 'r'), 60), ((51, Just 's'), 60), ((51, Just 't'), 60), ((51, Just 'u'), 60), ((51, Just 'v'), 60), ((51, Just 'w'), 60), ((51, Just 'x'), 60), ((51, Just 'y'), 60), ((51, Just 'z'), 60)
            , ((52, Just '0'), 60), ((52, Just '1'), 60), ((52, Just '2'), 60), ((52, Just '3'), 60), ((52, Just '4'), 60), ((52, Just '5'), 60), ((52, Just '6'), 60), ((52, Just '7'), 60), ((52, Just '8'), 60), ((52, Just '9'), 60), ((52, Just 'A'), 60), ((52, Just 'B'), 60), ((52, Just 'C'), 60), ((52, Just 'D'), 60), ((52, Just 'E'), 60), ((52, Just 'F'), 60), ((52, Just 'G'), 60), ((52, Just 'H'), 60), ((52, Just 'I'), 60), ((52, Just 'J'), 60), ((52, Just 'K'), 60), ((52, Just 'L'), 60), ((52, Just 'M'), 60), ((52, Just 'N'), 60), ((52, Just 'O'), 60), ((52, Just 'P'), 60), ((52, Just 'Q'), 60), ((52, Just 'R'), 60), ((52, Just 'S'), 60), ((52, Just 'T'), 60), ((52, Just 'U'), 60), ((52, Just 'V'), 60), ((52, Just 'W'), 60), ((52, Just 'X'), 60), ((52, Just 'Y'), 60), ((52, Just 'Z'), 60), ((52, Just '_'), 60), ((52, Just 'a'), 60), ((52, Just 'b'), 60), ((52, Just 'c'), 60), ((52, Just 'd'), 60), ((52, Just 'e'), 60), ((52, Just 'f'), 60), ((52, Just 'g'), 60), ((52, Just 'h'), 60), ((52, Just 'i'), 60), ((52, Just 'j'), 60), ((52, Just 'k'), 60), ((52, Just 'l'), 60), ((52, Just 'm'), 60), ((52, Just 'n'), 60), ((52, Just 'o'), 60), ((52, Just 'p'), 60), ((52, Just 'q'), 60), ((52, Just 'r'), 60), ((52, Just 's'), 60), ((52, Just 't'), 60), ((52, Just 'u'), 63), ((52, Just 'v'), 60), ((52, Just 'w'), 60), ((52, Just 'x'), 60), ((52, Just 'y'), 60), ((52, Just 'z'), 60)
            , ((53, Just '0'), 60), ((53, Just '1'), 60), ((53, Just '2'), 60), ((53, Just '3'), 60), ((53, Just '4'), 60), ((53, Just '5'), 60), ((53, Just '6'), 60), ((53, Just '7'), 60), ((53, Just '8'), 60), ((53, Just '9'), 60), ((53, Just 'A'), 60), ((53, Just 'B'), 60), ((53, Just 'C'), 60), ((53, Just 'D'), 60), ((53, Just 'E'), 60), ((53, Just 'F'), 60), ((53, Just 'G'), 60), ((53, Just 'H'), 60), ((53, Just 'I'), 60), ((53, Just 'J'), 60), ((53, Just 'K'), 60), ((53, Just 'L'), 60), ((53, Just 'M'), 60), ((53, Just 'N'), 60), ((53, Just 'O'), 60), ((53, Just 'P'), 60), ((53, Just 'Q'), 60), ((53, Just 'R'), 60), ((53, Just 'S'), 60), ((53, Just 'T'), 60), ((53, Just 'U'), 60), ((53, Just 'V'), 60), ((53, Just 'W'), 60), ((53, Just 'X'), 60), ((53, Just 'Y'), 60), ((53, Just 'Z'), 60), ((53, Just '_'), 60), ((53, Just 'a'), 60), ((53, Just 'b'), 60), ((53, Just 'c'), 60), ((53, Just 'd'), 60), ((53, Just 'e'), 60), ((53, Just 'f'), 60), ((53, Just 'g'), 60), ((53, Just 'h'), 60), ((53, Just 'i'), 60), ((53, Just 'j'), 60), ((53, Just 'k'), 60), ((53, Just 'l'), 60), ((53, Just 'm'), 60), ((53, Just 'n'), 60), ((53, Just 'o'), 60), ((53, Just 'p'), 64), ((53, Just 'q'), 60), ((53, Just 'r'), 60), ((53, Just 's'), 60), ((53, Just 't'), 60), ((53, Just 'u'), 60), ((53, Just 'v'), 60), ((53, Just 'w'), 60), ((53, Just 'x'), 60), ((53, Just 'y'), 60), ((53, Just 'z'), 60)
            , ((54, Just '0'), 60), ((54, Just '1'), 60), ((54, Just '2'), 60), ((54, Just '3'), 60), ((54, Just '4'), 60), ((54, Just '5'), 60), ((54, Just '6'), 60), ((54, Just '7'), 60), ((54, Just '8'), 60), ((54, Just '9'), 60), ((54, Just 'A'), 60), ((54, Just 'B'), 60), ((54, Just 'C'), 60), ((54, Just 'D'), 60), ((54, Just 'E'), 60), ((54, Just 'F'), 60), ((54, Just 'G'), 60), ((54, Just 'H'), 60), ((54, Just 'I'), 60), ((54, Just 'J'), 60), ((54, Just 'K'), 60), ((54, Just 'L'), 60), ((54, Just 'M'), 60), ((54, Just 'N'), 60), ((54, Just 'O'), 60), ((54, Just 'P'), 60), ((54, Just 'Q'), 60), ((54, Just 'R'), 60), ((54, Just 'S'), 60), ((54, Just 'T'), 60), ((54, Just 'U'), 60), ((54, Just 'V'), 60), ((54, Just 'W'), 60), ((54, Just 'X'), 60), ((54, Just 'Y'), 60), ((54, Just 'Z'), 60), ((54, Just '_'), 60), ((54, Just 'a'), 60), ((54, Just 'b'), 60), ((54, Just 'c'), 60), ((54, Just 'd'), 60), ((54, Just 'e'), 60), ((54, Just 'f'), 60), ((54, Just 'g'), 60), ((54, Just 'h'), 60), ((54, Just 'i'), 60), ((54, Just 'j'), 60), ((54, Just 'k'), 60), ((54, Just 'l'), 60), ((54, Just 'm'), 60), ((54, Just 'n'), 60), ((54, Just 'o'), 60), ((54, Just 'p'), 60), ((54, Just 'q'), 60), ((54, Just 'r'), 52), ((54, Just 's'), 60), ((54, Just 't'), 60), ((54, Just 'u'), 60), ((54, Just 'v'), 60), ((54, Just 'w'), 60), ((54, Just 'x'), 60), ((54, Just 'y'), 53), ((54, Just 'z'), 60)
            , ((55, Just '0'), 60), ((55, Just '1'), 60), ((55, Just '2'), 60), ((55, Just '3'), 60), ((55, Just '4'), 60), ((55, Just '5'), 60), ((55, Just '6'), 60), ((55, Just '7'), 60), ((55, Just '8'), 60), ((55, Just '9'), 60), ((55, Just 'A'), 60), ((55, Just 'B'), 60), ((55, Just 'C'), 60), ((55, Just 'D'), 60), ((55, Just 'E'), 60), ((55, Just 'F'), 60), ((55, Just 'G'), 60), ((55, Just 'H'), 60), ((55, Just 'I'), 60), ((55, Just 'J'), 60), ((55, Just 'K'), 60), ((55, Just 'L'), 60), ((55, Just 'M'), 60), ((55, Just 'N'), 60), ((55, Just 'O'), 60), ((55, Just 'P'), 60), ((55, Just 'Q'), 60), ((55, Just 'R'), 60), ((55, Just 'S'), 60), ((55, Just 'T'), 60), ((55, Just 'U'), 60), ((55, Just 'V'), 60), ((55, Just 'W'), 60), ((55, Just 'X'), 60), ((55, Just 'Y'), 60), ((55, Just 'Z'), 60), ((55, Just '_'), 60), ((55, Just 'a'), 60), ((55, Just 'b'), 60), ((55, Just 'c'), 60), ((55, Just 'd'), 60), ((55, Just 'e'), 60), ((55, Just 'f'), 60), ((55, Just 'g'), 60), ((55, Just 'h'), 60), ((55, Just 'i'), 60), ((55, Just 'j'), 60), ((55, Just 'k'), 60), ((55, Just 'l'), 60), ((55, Just 'm'), 60), ((55, Just 'n'), 60), ((55, Just 'o'), 60), ((55, Just 'p'), 60), ((55, Just 'q'), 60), ((55, Just 'r'), 60), ((55, Just 's'), 60), ((55, Just 't'), 60), ((55, Just 'u'), 65), ((55, Just 'v'), 60), ((55, Just 'w'), 60), ((55, Just 'x'), 60), ((55, Just 'y'), 60), ((55, Just 'z'), 60)
            , ((56, Just '0'), 60), ((56, Just '1'), 60), ((56, Just '2'), 60), ((56, Just '3'), 60), ((56, Just '4'), 60), ((56, Just '5'), 60), ((56, Just '6'), 60), ((56, Just '7'), 60), ((56, Just '8'), 60), ((56, Just '9'), 60), ((56, Just 'A'), 60), ((56, Just 'B'), 60), ((56, Just 'C'), 60), ((56, Just 'D'), 60), ((56, Just 'E'), 60), ((56, Just 'F'), 60), ((56, Just 'G'), 60), ((56, Just 'H'), 60), ((56, Just 'I'), 60), ((56, Just 'J'), 60), ((56, Just 'K'), 60), ((56, Just 'L'), 60), ((56, Just 'M'), 60), ((56, Just 'N'), 60), ((56, Just 'O'), 60), ((56, Just 'P'), 60), ((56, Just 'Q'), 60), ((56, Just 'R'), 60), ((56, Just 'S'), 60), ((56, Just 'T'), 60), ((56, Just 'U'), 60), ((56, Just 'V'), 60), ((56, Just 'W'), 60), ((56, Just 'X'), 60), ((56, Just 'Y'), 60), ((56, Just 'Z'), 60), ((56, Just '_'), 60), ((56, Just 'a'), 60), ((56, Just 'b'), 55), ((56, Just 'c'), 60), ((56, Just 'd'), 60), ((56, Just 'e'), 60), ((56, Just 'f'), 60), ((56, Just 'g'), 60), ((56, Just 'h'), 60), ((56, Just 'i'), 60), ((56, Just 'j'), 60), ((56, Just 'k'), 60), ((56, Just 'l'), 60), ((56, Just 'm'), 60), ((56, Just 'n'), 60), ((56, Just 'o'), 60), ((56, Just 'p'), 60), ((56, Just 'q'), 60), ((56, Just 'r'), 60), ((56, Just 's'), 60), ((56, Just 't'), 60), ((56, Just 'u'), 60), ((56, Just 'v'), 60), ((56, Just 'w'), 60), ((56, Just 'x'), 60), ((56, Just 'y'), 60), ((56, Just 'z'), 60)
            , ((57, Just '0'), 60), ((57, Just '1'), 60), ((57, Just '2'), 60), ((57, Just '3'), 60), ((57, Just '4'), 60), ((57, Just '5'), 60), ((57, Just '6'), 60), ((57, Just '7'), 60), ((57, Just '8'), 60), ((57, Just '9'), 60), ((57, Just 'A'), 60), ((57, Just 'B'), 60), ((57, Just 'C'), 60), ((57, Just 'D'), 60), ((57, Just 'E'), 60), ((57, Just 'F'), 60), ((57, Just 'G'), 60), ((57, Just 'H'), 60), ((57, Just 'I'), 60), ((57, Just 'J'), 60), ((57, Just 'K'), 60), ((57, Just 'L'), 60), ((57, Just 'M'), 60), ((57, Just 'N'), 60), ((57, Just 'O'), 60), ((57, Just 'P'), 60), ((57, Just 'Q'), 60), ((57, Just 'R'), 60), ((57, Just 'S'), 60), ((57, Just 'T'), 60), ((57, Just 'U'), 60), ((57, Just 'V'), 60), ((57, Just 'W'), 60), ((57, Just 'X'), 60), ((57, Just 'Y'), 60), ((57, Just 'Z'), 60), ((57, Just '_'), 60), ((57, Just 'a'), 60), ((57, Just 'b'), 60), ((57, Just 'c'), 60), ((57, Just 'd'), 60), ((57, Just 'e'), 56), ((57, Just 'f'), 60), ((57, Just 'g'), 60), ((57, Just 'h'), 60), ((57, Just 'i'), 60), ((57, Just 'j'), 60), ((57, Just 'k'), 60), ((57, Just 'l'), 60), ((57, Just 'm'), 60), ((57, Just 'n'), 60), ((57, Just 'o'), 60), ((57, Just 'p'), 60), ((57, Just 'q'), 60), ((57, Just 'r'), 60), ((57, Just 's'), 60), ((57, Just 't'), 60), ((57, Just 'u'), 60), ((57, Just 'v'), 60), ((57, Just 'w'), 60), ((57, Just 'x'), 60), ((57, Just 'y'), 60), ((57, Just 'z'), 60)
            , ((58, Just '0'), 60), ((58, Just '1'), 60), ((58, Just '2'), 60), ((58, Just '3'), 60), ((58, Just '4'), 60), ((58, Just '5'), 60), ((58, Just '6'), 60), ((58, Just '7'), 60), ((58, Just '8'), 60), ((58, Just '9'), 60), ((58, Just 'A'), 60), ((58, Just 'B'), 60), ((58, Just 'C'), 60), ((58, Just 'D'), 60), ((58, Just 'E'), 60), ((58, Just 'F'), 60), ((58, Just 'G'), 60), ((58, Just 'H'), 60), ((58, Just 'I'), 60), ((58, Just 'J'), 60), ((58, Just 'K'), 60), ((58, Just 'L'), 60), ((58, Just 'M'), 60), ((58, Just 'N'), 60), ((58, Just 'O'), 60), ((58, Just 'P'), 60), ((58, Just 'Q'), 60), ((58, Just 'R'), 60), ((58, Just 'S'), 60), ((58, Just 'T'), 60), ((58, Just 'U'), 60), ((58, Just 'V'), 60), ((58, Just 'W'), 60), ((58, Just 'X'), 60), ((58, Just 'Y'), 60), ((58, Just 'Z'), 60), ((58, Just '_'), 60), ((58, Just 'a'), 60), ((58, Just 'b'), 60), ((58, Just 'c'), 60), ((58, Just 'd'), 60), ((58, Just 'e'), 60), ((58, Just 'f'), 60), ((58, Just 'g'), 60), ((58, Just 'h'), 60), ((58, Just 'i'), 66), ((58, Just 'j'), 60), ((58, Just 'k'), 60), ((58, Just 'l'), 60), ((58, Just 'm'), 60), ((58, Just 'n'), 60), ((58, Just 'o'), 60), ((58, Just 'p'), 60), ((58, Just 'q'), 60), ((58, Just 'r'), 60), ((58, Just 's'), 60), ((58, Just 't'), 60), ((58, Just 'u'), 60), ((58, Just 'v'), 60), ((58, Just 'w'), 60), ((58, Just 'x'), 60), ((58, Just 'y'), 60), ((58, Just 'z'), 60)
            , ((59, Just '0'), 60), ((59, Just '1'), 60), ((59, Just '2'), 60), ((59, Just '3'), 60), ((59, Just '4'), 60), ((59, Just '5'), 60), ((59, Just '6'), 60), ((59, Just '7'), 60), ((59, Just '8'), 60), ((59, Just '9'), 60), ((59, Just 'A'), 60), ((59, Just 'B'), 60), ((59, Just 'C'), 60), ((59, Just 'D'), 60), ((59, Just 'E'), 60), ((59, Just 'F'), 60), ((59, Just 'G'), 60), ((59, Just 'H'), 60), ((59, Just 'I'), 60), ((59, Just 'J'), 60), ((59, Just 'K'), 60), ((59, Just 'L'), 60), ((59, Just 'M'), 60), ((59, Just 'N'), 60), ((59, Just 'O'), 60), ((59, Just 'P'), 60), ((59, Just 'Q'), 60), ((59, Just 'R'), 60), ((59, Just 'S'), 60), ((59, Just 'T'), 60), ((59, Just 'U'), 60), ((59, Just 'V'), 60), ((59, Just 'W'), 60), ((59, Just 'X'), 60), ((59, Just 'Y'), 60), ((59, Just 'Z'), 60), ((59, Just '_'), 60), ((59, Just 'a'), 58), ((59, Just 'b'), 60), ((59, Just 'c'), 60), ((59, Just 'd'), 60), ((59, Just 'e'), 60), ((59, Just 'f'), 60), ((59, Just 'g'), 60), ((59, Just 'h'), 60), ((59, Just 'i'), 60), ((59, Just 'j'), 60), ((59, Just 'k'), 60), ((59, Just 'l'), 60), ((59, Just 'm'), 60), ((59, Just 'n'), 60), ((59, Just 'o'), 60), ((59, Just 'p'), 60), ((59, Just 'q'), 60), ((59, Just 'r'), 60), ((59, Just 's'), 60), ((59, Just 't'), 60), ((59, Just 'u'), 60), ((59, Just 'v'), 60), ((59, Just 'w'), 60), ((59, Just 'x'), 60), ((59, Just 'y'), 60), ((59, Just 'z'), 60)
            , ((60, Just '0'), 60), ((60, Just '1'), 60), ((60, Just '2'), 60), ((60, Just '3'), 60), ((60, Just '4'), 60), ((60, Just '5'), 60), ((60, Just '6'), 60), ((60, Just '7'), 60), ((60, Just '8'), 60), ((60, Just '9'), 60), ((60, Just 'A'), 60), ((60, Just 'B'), 60), ((60, Just 'C'), 60), ((60, Just 'D'), 60), ((60, Just 'E'), 60), ((60, Just 'F'), 60), ((60, Just 'G'), 60), ((60, Just 'H'), 60), ((60, Just 'I'), 60), ((60, Just 'J'), 60), ((60, Just 'K'), 60), ((60, Just 'L'), 60), ((60, Just 'M'), 60), ((60, Just 'N'), 60), ((60, Just 'O'), 60), ((60, Just 'P'), 60), ((60, Just 'Q'), 60), ((60, Just 'R'), 60), ((60, Just 'S'), 60), ((60, Just 'T'), 60), ((60, Just 'U'), 60), ((60, Just 'V'), 60), ((60, Just 'W'), 60), ((60, Just 'X'), 60), ((60, Just 'Y'), 60), ((60, Just 'Z'), 60), ((60, Just '_'), 60), ((60, Just 'a'), 60), ((60, Just 'b'), 60), ((60, Just 'c'), 60), ((60, Just 'd'), 60), ((60, Just 'e'), 60), ((60, Just 'f'), 60), ((60, Just 'g'), 60), ((60, Just 'h'), 60), ((60, Just 'i'), 60), ((60, Just 'j'), 60), ((60, Just 'k'), 60), ((60, Just 'l'), 60), ((60, Just 'm'), 60), ((60, Just 'n'), 60), ((60, Just 'o'), 60), ((60, Just 'p'), 60), ((60, Just 'q'), 60), ((60, Just 'r'), 60), ((60, Just 's'), 60), ((60, Just 't'), 60), ((60, Just 'u'), 60), ((60, Just 'v'), 60), ((60, Just 'w'), 60), ((60, Just 'x'), 60), ((60, Just 'y'), 60), ((60, Just 'z'), 60)
            , ((61, Just '0'), 60), ((61, Just '1'), 60), ((61, Just '2'), 60), ((61, Just '3'), 60), ((61, Just '4'), 60), ((61, Just '5'), 60), ((61, Just '6'), 60), ((61, Just '7'), 60), ((61, Just '8'), 60), ((61, Just '9'), 60), ((61, Just 'A'), 60), ((61, Just 'B'), 60), ((61, Just 'C'), 60), ((61, Just 'D'), 60), ((61, Just 'E'), 60), ((61, Just 'F'), 60), ((61, Just 'G'), 60), ((61, Just 'H'), 60), ((61, Just 'I'), 60), ((61, Just 'J'), 60), ((61, Just 'K'), 60), ((61, Just 'L'), 60), ((61, Just 'M'), 60), ((61, Just 'N'), 60), ((61, Just 'O'), 60), ((61, Just 'P'), 60), ((61, Just 'Q'), 60), ((61, Just 'R'), 60), ((61, Just 'S'), 60), ((61, Just 'T'), 60), ((61, Just 'U'), 60), ((61, Just 'V'), 60), ((61, Just 'W'), 60), ((61, Just 'X'), 60), ((61, Just 'Y'), 60), ((61, Just 'Z'), 60), ((61, Just '_'), 60), ((61, Just 'a'), 35), ((61, Just 'b'), 60), ((61, Just 'c'), 60), ((61, Just 'd'), 60), ((61, Just 'e'), 60), ((61, Just 'f'), 60), ((61, Just 'g'), 60), ((61, Just 'h'), 60), ((61, Just 'i'), 60), ((61, Just 'j'), 60), ((61, Just 'k'), 60), ((61, Just 'l'), 60), ((61, Just 'm'), 60), ((61, Just 'n'), 60), ((61, Just 'o'), 60), ((61, Just 'p'), 60), ((61, Just 'q'), 60), ((61, Just 'r'), 60), ((61, Just 's'), 60), ((61, Just 't'), 60), ((61, Just 'u'), 60), ((61, Just 'v'), 60), ((61, Just 'w'), 60), ((61, Just 'x'), 60), ((61, Just 'y'), 60), ((61, Just 'z'), 60)
            , ((62, Just '0'), 60), ((62, Just '1'), 60), ((62, Just '2'), 60), ((62, Just '3'), 60), ((62, Just '4'), 60), ((62, Just '5'), 60), ((62, Just '6'), 60), ((62, Just '7'), 60), ((62, Just '8'), 60), ((62, Just '9'), 60), ((62, Just 'A'), 60), ((62, Just 'B'), 60), ((62, Just 'C'), 60), ((62, Just 'D'), 60), ((62, Just 'E'), 60), ((62, Just 'F'), 60), ((62, Just 'G'), 60), ((62, Just 'H'), 60), ((62, Just 'I'), 60), ((62, Just 'J'), 60), ((62, Just 'K'), 60), ((62, Just 'L'), 60), ((62, Just 'M'), 60), ((62, Just 'N'), 60), ((62, Just 'O'), 60), ((62, Just 'P'), 60), ((62, Just 'Q'), 60), ((62, Just 'R'), 60), ((62, Just 'S'), 60), ((62, Just 'T'), 60), ((62, Just 'U'), 60), ((62, Just 'V'), 60), ((62, Just 'W'), 60), ((62, Just 'X'), 60), ((62, Just 'Y'), 60), ((62, Just 'Z'), 60), ((62, Just '_'), 60), ((62, Just 'a'), 60), ((62, Just 'b'), 60), ((62, Just 'c'), 60), ((62, Just 'd'), 44), ((62, Just 'e'), 60), ((62, Just 'f'), 60), ((62, Just 'g'), 60), ((62, Just 'h'), 60), ((62, Just 'i'), 60), ((62, Just 'j'), 60), ((62, Just 'k'), 60), ((62, Just 'l'), 60), ((62, Just 'm'), 60), ((62, Just 'n'), 60), ((62, Just 'o'), 60), ((62, Just 'p'), 60), ((62, Just 'q'), 60), ((62, Just 'r'), 60), ((62, Just 's'), 60), ((62, Just 't'), 60), ((62, Just 'u'), 60), ((62, Just 'v'), 60), ((62, Just 'w'), 60), ((62, Just 'x'), 60), ((62, Just 'y'), 60), ((62, Just 'z'), 60)
            , ((63, Just '0'), 60), ((63, Just '1'), 60), ((63, Just '2'), 60), ((63, Just '3'), 60), ((63, Just '4'), 60), ((63, Just '5'), 60), ((63, Just '6'), 60), ((63, Just '7'), 60), ((63, Just '8'), 60), ((63, Just '9'), 60), ((63, Just 'A'), 60), ((63, Just 'B'), 60), ((63, Just 'C'), 60), ((63, Just 'D'), 60), ((63, Just 'E'), 60), ((63, Just 'F'), 60), ((63, Just 'G'), 60), ((63, Just 'H'), 60), ((63, Just 'I'), 60), ((63, Just 'J'), 60), ((63, Just 'K'), 60), ((63, Just 'L'), 60), ((63, Just 'M'), 60), ((63, Just 'N'), 60), ((63, Just 'O'), 60), ((63, Just 'P'), 60), ((63, Just 'Q'), 60), ((63, Just 'R'), 60), ((63, Just 'S'), 60), ((63, Just 'T'), 60), ((63, Just 'U'), 60), ((63, Just 'V'), 60), ((63, Just 'W'), 60), ((63, Just 'X'), 60), ((63, Just 'Y'), 60), ((63, Just 'Z'), 60), ((63, Just '_'), 60), ((63, Just 'a'), 60), ((63, Just 'b'), 60), ((63, Just 'c'), 60), ((63, Just 'd'), 60), ((63, Just 'e'), 38), ((63, Just 'f'), 60), ((63, Just 'g'), 60), ((63, Just 'h'), 60), ((63, Just 'i'), 60), ((63, Just 'j'), 60), ((63, Just 'k'), 60), ((63, Just 'l'), 60), ((63, Just 'm'), 60), ((63, Just 'n'), 60), ((63, Just 'o'), 60), ((63, Just 'p'), 60), ((63, Just 'q'), 60), ((63, Just 'r'), 60), ((63, Just 's'), 60), ((63, Just 't'), 60), ((63, Just 'u'), 60), ((63, Just 'v'), 60), ((63, Just 'w'), 60), ((63, Just 'x'), 60), ((63, Just 'y'), 60), ((63, Just 'z'), 60)
            , ((64, Just '0'), 60), ((64, Just '1'), 60), ((64, Just '2'), 60), ((64, Just '3'), 60), ((64, Just '4'), 60), ((64, Just '5'), 60), ((64, Just '6'), 60), ((64, Just '7'), 60), ((64, Just '8'), 60), ((64, Just '9'), 60), ((64, Just 'A'), 60), ((64, Just 'B'), 60), ((64, Just 'C'), 60), ((64, Just 'D'), 60), ((64, Just 'E'), 60), ((64, Just 'F'), 60), ((64, Just 'G'), 60), ((64, Just 'H'), 60), ((64, Just 'I'), 60), ((64, Just 'J'), 60), ((64, Just 'K'), 60), ((64, Just 'L'), 60), ((64, Just 'M'), 60), ((64, Just 'N'), 60), ((64, Just 'O'), 60), ((64, Just 'P'), 60), ((64, Just 'Q'), 60), ((64, Just 'R'), 60), ((64, Just 'S'), 60), ((64, Just 'T'), 60), ((64, Just 'U'), 60), ((64, Just 'V'), 60), ((64, Just 'W'), 60), ((64, Just 'X'), 60), ((64, Just 'Y'), 60), ((64, Just 'Z'), 60), ((64, Just '_'), 60), ((64, Just 'a'), 60), ((64, Just 'b'), 60), ((64, Just 'c'), 60), ((64, Just 'd'), 60), ((64, Just 'e'), 45), ((64, Just 'f'), 60), ((64, Just 'g'), 60), ((64, Just 'h'), 60), ((64, Just 'i'), 60), ((64, Just 'j'), 60), ((64, Just 'k'), 60), ((64, Just 'l'), 60), ((64, Just 'm'), 60), ((64, Just 'n'), 60), ((64, Just 'o'), 60), ((64, Just 'p'), 60), ((64, Just 'q'), 60), ((64, Just 'r'), 60), ((64, Just 's'), 60), ((64, Just 't'), 60), ((64, Just 'u'), 60), ((64, Just 'v'), 60), ((64, Just 'w'), 60), ((64, Just 'x'), 60), ((64, Just 'y'), 60), ((64, Just 'z'), 60)
            , ((65, Just '0'), 60), ((65, Just '1'), 60), ((65, Just '2'), 60), ((65, Just '3'), 60), ((65, Just '4'), 60), ((65, Just '5'), 60), ((65, Just '6'), 60), ((65, Just '7'), 60), ((65, Just '8'), 60), ((65, Just '9'), 60), ((65, Just 'A'), 60), ((65, Just 'B'), 60), ((65, Just 'C'), 60), ((65, Just 'D'), 60), ((65, Just 'E'), 60), ((65, Just 'F'), 60), ((65, Just 'G'), 60), ((65, Just 'H'), 60), ((65, Just 'I'), 60), ((65, Just 'J'), 60), ((65, Just 'K'), 60), ((65, Just 'L'), 60), ((65, Just 'M'), 60), ((65, Just 'N'), 60), ((65, Just 'O'), 60), ((65, Just 'P'), 60), ((65, Just 'Q'), 60), ((65, Just 'R'), 60), ((65, Just 'S'), 60), ((65, Just 'T'), 60), ((65, Just 'U'), 60), ((65, Just 'V'), 60), ((65, Just 'W'), 60), ((65, Just 'X'), 60), ((65, Just 'Y'), 60), ((65, Just 'Z'), 60), ((65, Just '_'), 60), ((65, Just 'a'), 60), ((65, Just 'b'), 60), ((65, Just 'c'), 60), ((65, Just 'd'), 60), ((65, Just 'e'), 60), ((65, Just 'f'), 60), ((65, Just 'g'), 41), ((65, Just 'h'), 60), ((65, Just 'i'), 60), ((65, Just 'j'), 60), ((65, Just 'k'), 60), ((65, Just 'l'), 60), ((65, Just 'm'), 60), ((65, Just 'n'), 60), ((65, Just 'o'), 60), ((65, Just 'p'), 60), ((65, Just 'q'), 60), ((65, Just 'r'), 60), ((65, Just 's'), 60), ((65, Just 't'), 60), ((65, Just 'u'), 60), ((65, Just 'v'), 60), ((65, Just 'w'), 60), ((65, Just 'x'), 60), ((65, Just 'y'), 60), ((65, Just 'z'), 60)
            , ((66, Just '0'), 60), ((66, Just '1'), 60), ((66, Just '2'), 60), ((66, Just '3'), 60), ((66, Just '4'), 60), ((66, Just '5'), 60), ((66, Just '6'), 60), ((66, Just '7'), 60), ((66, Just '8'), 60), ((66, Just '9'), 60), ((66, Just 'A'), 60), ((66, Just 'B'), 60), ((66, Just 'C'), 60), ((66, Just 'D'), 60), ((66, Just 'E'), 60), ((66, Just 'F'), 60), ((66, Just 'G'), 60), ((66, Just 'H'), 60), ((66, Just 'I'), 60), ((66, Just 'J'), 60), ((66, Just 'K'), 60), ((66, Just 'L'), 60), ((66, Just 'M'), 60), ((66, Just 'N'), 60), ((66, Just 'O'), 60), ((66, Just 'P'), 60), ((66, Just 'Q'), 60), ((66, Just 'R'), 60), ((66, Just 'S'), 60), ((66, Just 'T'), 60), ((66, Just 'U'), 60), ((66, Just 'V'), 60), ((66, Just 'W'), 60), ((66, Just 'X'), 60), ((66, Just 'Y'), 60), ((66, Just 'Z'), 60), ((66, Just '_'), 60), ((66, Just 'a'), 60), ((66, Just 'b'), 60), ((66, Just 'c'), 60), ((66, Just 'd'), 60), ((66, Just 'e'), 60), ((66, Just 'f'), 60), ((66, Just 'g'), 60), ((66, Just 'h'), 60), ((66, Just 'i'), 60), ((66, Just 'j'), 60), ((66, Just 'k'), 60), ((66, Just 'l'), 39), ((66, Just 'm'), 60), ((66, Just 'n'), 60), ((66, Just 'o'), 60), ((66, Just 'p'), 60), ((66, Just 'q'), 60), ((66, Just 'r'), 60), ((66, Just 's'), 60), ((66, Just 't'), 60), ((66, Just 'u'), 60), ((66, Just 'v'), 60), ((66, Just 'w'), 60), ((66, Just 'x'), 60), ((66, Just 'y'), 60), ((66, Just 'z'), 60)
            , ((67, Just '0'), 60), ((67, Just '1'), 60), ((67, Just '2'), 60), ((67, Just '3'), 60), ((67, Just '4'), 60), ((67, Just '5'), 60), ((67, Just '6'), 60), ((67, Just '7'), 60), ((67, Just '8'), 60), ((67, Just '9'), 60), ((67, Just 'A'), 60), ((67, Just 'B'), 60), ((67, Just 'C'), 60), ((67, Just 'D'), 60), ((67, Just 'E'), 60), ((67, Just 'F'), 60), ((67, Just 'G'), 60), ((67, Just 'H'), 60), ((67, Just 'I'), 60), ((67, Just 'J'), 60), ((67, Just 'K'), 60), ((67, Just 'L'), 60), ((67, Just 'M'), 60), ((67, Just 'N'), 60), ((67, Just 'O'), 60), ((67, Just 'P'), 60), ((67, Just 'Q'), 60), ((67, Just 'R'), 60), ((67, Just 'S'), 60), ((67, Just 'T'), 60), ((67, Just 'U'), 60), ((67, Just 'V'), 60), ((67, Just 'W'), 60), ((67, Just 'X'), 60), ((67, Just 'Y'), 60), ((67, Just 'Z'), 60), ((67, Just '_'), 60), ((67, Just 'a'), 60), ((67, Just 'b'), 60), ((67, Just 'c'), 60), ((67, Just 'd'), 60), ((67, Just 'e'), 60), ((67, Just 'f'), 60), ((67, Just 'g'), 60), ((67, Just 'h'), 60), ((67, Just 'i'), 60), ((67, Just 'j'), 60), ((67, Just 'k'), 60), ((67, Just 'l'), 60), ((67, Just 'm'), 60), ((67, Just 'n'), 60), ((67, Just 'o'), 60), ((67, Just 'p'), 60), ((67, Just 'q'), 60), ((67, Just 'r'), 60), ((67, Just 's'), 40), ((67, Just 't'), 60), ((67, Just 'u'), 60), ((67, Just 'v'), 60), ((67, Just 'w'), 60), ((67, Just 'x'), 60), ((67, Just 'y'), 60), ((67, Just 'z'), 60)
            , ((68, Just '0'), 68), ((68, Just '1'), 68), ((68, Just '2'), 68), ((68, Just '3'), 68), ((68, Just '4'), 68), ((68, Just '5'), 68), ((68, Just '6'), 68), ((68, Just '7'), 68), ((68, Just '8'), 68), ((68, Just '9'), 68)
            , ((71, Just '\t'), 71), ((71, Just '\n'), 71), ((71, Just '\r'), 71), ((71, Just ' '), 71)
            , ((72, Just '\t'), 72), ((72, Just '\r'), 72), ((72, Just ' '), 72), ((72, Just '!'), 72), ((72, Just '"'), 72), ((72, Just '%'), 72), ((72, Just '\''), 72), ((72, Just '('), 72), ((72, Just ')'), 72), ((72, Just '*'), 72), ((72, Just '+'), 72), ((72, Just ','), 72), ((72, Just '-'), 72), ((72, Just '.'), 72), ((72, Just '/'), 72), ((72, Just '0'), 72), ((72, Just '1'), 72), ((72, Just '2'), 72), ((72, Just '3'), 72), ((72, Just '4'), 72), ((72, Just '5'), 72), ((72, Just '6'), 72), ((72, Just '7'), 72), ((72, Just '8'), 72), ((72, Just '9'), 72), ((72, Just ':'), 72), ((72, Just ';'), 72), ((72, Just '<'), 72), ((72, Just '='), 72), ((72, Just '>'), 72), ((72, Just '?'), 72), ((72, Just 'A'), 72), ((72, Just 'B'), 72), ((72, Just 'C'), 72), ((72, Just 'D'), 72), ((72, Just 'E'), 72), ((72, Just 'F'), 72), ((72, Just 'G'), 72), ((72, Just 'H'), 72), ((72, Just 'I'), 72), ((72, Just 'J'), 72), ((72, Just 'K'), 72), ((72, Just 'L'), 72), ((72, Just 'M'), 72), ((72, Just 'N'), 72), ((72, Just 'O'), 72), ((72, Just 'P'), 72), ((72, Just 'Q'), 72), ((72, Just 'R'), 72), ((72, Just 'S'), 72), ((72, Just 'T'), 72), ((72, Just 'U'), 72), ((72, Just 'V'), 72), ((72, Just 'W'), 72), ((72, Just 'X'), 72), ((72, Just 'Y'), 72), ((72, Just 'Z'), 72), ((72, Just '['), 72), ((72, Just '\\'), 72), ((72, Just ']'), 72), ((72, Just '_'), 72), ((72, Just '`'), 72), ((72, Just 'a'), 72), ((72, Just 'b'), 72), ((72, Just 'c'), 72), ((72, Just 'd'), 72), ((72, Just 'e'), 72), ((72, Just 'f'), 72), ((72, Just 'g'), 72), ((72, Just 'h'), 72), ((72, Just 'i'), 72), ((72, Just 'j'), 72), ((72, Just 'k'), 72), ((72, Just 'l'), 72), ((72, Just 'm'), 72), ((72, Just 'n'), 72), ((72, Just 'o'), 72), ((72, Just 'p'), 72), ((72, Just 'q'), 72), ((72, Just 'r'), 72), ((72, Just 's'), 72), ((72, Just 't'), 72), ((72, Just 'u'), 72), ((72, Just 'v'), 72), ((72, Just 'w'), 72), ((72, Just 'x'), 72), ((72, Just 'y'), 72), ((72, Just 'z'), 72), ((72, Nothing), 72)
            ]
        }
    theAlphabet :: XSet.Set Char
    theAlphabet = XSet.fromAscList "\t\n\r !\"%'()*+,-./0123456789:;<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]_`abcdefghijklmnopqrstuvwxyz"
    runDFA :: DFA -> [((Int, Int), Char)] -> Either (Int, Int) ((Maybe Int, [((Int, Int), Char)]), [((Int, Int), Char)])
    runDFA (DFA q0 qfs deltas) = Right . XIdentity.runIdentity . runFast where
        classify :: Char -> Maybe Char
        classify ch = if ch `XSet.member` theAlphabet then Just ch else Nothing
        loop1 :: Int -> [((Int, Int), Char)] -> [((Int, Int), Char)] -> XState.StateT (Maybe Int, [((Int, Int), Char)]) XIdentity.Identity [((Int, Int), Char)]
        loop1 q buffer [] = return buffer
        loop1 q buffer (ch : str) = do
            (latest, accepted) <- XState.get
            case XMap.lookup (q, classify (snd ch)) deltas of
                Nothing -> return (buffer ++ [ch] ++ str)
                Just p -> case XMap.lookup p qfs of
                    Nothing -> loop1 p (buffer ++ [ch]) str
                    latest' -> do
                        XState.put (latest', accepted ++ buffer ++ [ch])
                        loop1 p [] str
        runFast :: [((Int, Int), Char)] -> XIdentity.Identity ((Maybe Int, [((Int, Int), Char)]), [((Int, Int), Char)])
        runFast input = do
            (rest, (latest, accepted)) <- XState.runStateT (loop1 q0 [] input) (Nothing, [])
            return ((latest, accepted), rest)
    addLoc :: Int -> Int -> String -> [((Int, Int), Char)]
    addLoc _ _ [] = []
    addLoc row col (ch : chs) = if ch == '\n' then ((row, col), ch) : addLoc (row + 1) 1 chs else ((row, col), ch) : addLoc row (col + 1) chs
    runHolLexerRaw_this :: [((Int, Int), Char)] -> Either (Int, Int) [Token]
    runHolLexerRaw_this [] = return []
    runHolLexerRaw_this str0 = do
        let return_one my_token = return [my_token]
        dfa_output <- runDFA theDFA str0
        (str1, piece) <- case dfa_output of
            ((_, []), _) -> Left (fst (head str0))
            ((Just label, accepted), rest) -> return (rest, ((label, map snd accepted), (fst (head accepted), fst (head (reverse accepted)))))
            _ -> Left (fst (head str0))
        tokens1 <- case piece of
            ((1, this), ((row1, col1), (row2, col2))) -> return_one (T_wildcard (SLoc (row1, col1) (row2, col2)))
            ((2, this), ((row1, col1), (row2, col2))) -> return_one (T_dot (SLoc (row1, col1) (row2, col2)))
            ((3, this), ((row1, col1), (row2, col2))) -> return_one (T_arrow (SLoc (row1, col1) (row2, col2)))
            ((4, this), ((row1, col1), (row2, col2))) -> return_one (T_fatarrow (SLoc (row1, col1) (row2, col2)))
            ((5, this), ((row1, col1), (row2, col2))) -> return_one (T_lparen (SLoc (row1, col1) (row2, col2)))
            ((6, this), ((row1, col1), (row2, col2))) -> return_one (T_rparen (SLoc (row1, col1) (row2, col2)))
            ((7, this), ((row1, col1), (row2, col2))) -> return_one (T_lbracket (SLoc (row1, col1) (row2, col2)))
            ((8, this), ((row1, col1), (row2, col2))) -> return_one (T_rbracket (SLoc (row1, col1) (row2, col2)))
            ((9, this), ((row1, col1), (row2, col2))) -> return_one (T_quest (SLoc (row1, col1) (row2, col2)))
            ((10, this), ((row1, col1), (row2, col2))) -> return_one (T_comma (SLoc (row1, col1) (row2, col2)))
            ((11, this), ((row1, col1), (row2, col2))) -> return_one (T_fatarrow (SLoc (row1, col1) (row2, col2)))
            ((12, this), ((row1, col1), (row2, col2))) -> return_one (T_if (SLoc (row1, col1) (row2, col2)))
            ((13, this), ((row1, col1), (row2, col2))) -> return_one (T_succ (SLoc (row1, col1) (row2, col2)))
            ((14, this), ((row1, col1), (row2, col2))) -> return_one (T_eq (SLoc (row1, col1) (row2, col2)))
            ((15, this), ((row1, col1), (row2, col2))) -> return_one (T_le (SLoc (row1, col1) (row2, col2)))
            ((16, this), ((row1, col1), (row2, col2))) -> return_one (T_lt (SLoc (row1, col1) (row2, col2)))
            ((17, this), ((row1, col1), (row2, col2))) -> return_one (T_ge (SLoc (row1, col1) (row2, col2)))
            ((18, this), ((row1, col1), (row2, col2))) -> return_one (T_gt (SLoc (row1, col1) (row2, col2)))
            ((19, this), ((row1, col1), (row2, col2))) -> return_one (T_plus (SLoc (row1, col1) (row2, col2)))
            ((20, this), ((row1, col1), (row2, col2))) -> return_one (T_minus (SLoc (row1, col1) (row2, col2)))
            ((21, this), ((row1, col1), (row2, col2))) -> return_one (T_star (SLoc (row1, col1) (row2, col2)))
            ((22, this), ((row1, col1), (row2, col2))) -> return_one (T_slash (SLoc (row1, col1) (row2, col2)))
            ((23, this), ((row1, col1), (row2, col2))) -> return_one (T_pi (SLoc (row1, col1) (row2, col2)))
            ((24, this), ((row1, col1), (row2, col2))) -> return_one (T_sigma (SLoc (row1, col1) (row2, col2)))
            ((25, this), ((row1, col1), (row2, col2))) -> return_one (T_semicolon (SLoc (row1, col1) (row2, col2)))
            ((26, this), ((row1, col1), (row2, col2))) -> return_one (T_cut (SLoc (row1, col1) (row2, col2)))
            ((27, this), ((row1, col1), (row2, col2))) -> return_one (T_true (SLoc (row1, col1) (row2, col2)))
            ((28, this), ((row1, col1), (row2, col2))) -> return_one (T_fail (SLoc (row1, col1) (row2, col2)))
            ((29, this), ((row1, col1), (row2, col2))) -> return_one (T_is (SLoc (row1, col1) (row2, col2)))
            ((30, this), ((row1, col1), (row2, col2))) -> return_one (T_debug (SLoc (row1, col1) (row2, col2)))
            ((31, this), ((row1, col1), (row2, col2))) -> return_one (T_bslash (SLoc (row1, col1) (row2, col2)))
            ((32, this), ((row1, col1), (row2, col2))) -> return_one (T_cons (SLoc (row1, col1) (row2, col2)))
            ((33, this), ((row1, col1), (row2, col2))) -> return_one (T_kind (SLoc (row1, col1) (row2, col2)))
            ((34, this), ((row1, col1), (row2, col2))) -> return_one (T_type (SLoc (row1, col1) (row2, col2)))
            ((35, this), ((row1, col1), (row2, col2))) -> return_one (T_id (SLoc (row1, col1) (row2, col2)) (init (tail this)))
            ((36, this), ((row1, col1), (row2, col2))) -> return_one (T_id (SLoc (row1, col1) (row2, col2)) this)
            ((37, this), ((row1, col1), (row2, col2))) -> return_one (T_nat_lit (SLoc (row1, col1) (row2, col2)) (read this))
            ((38, this), ((row1, col1), (row2, col2))) -> return_one (mkStringToken (SLoc (row1, col1) (row2, col2)) this)
            ((39, this), ((row1, col1), (row2, col2))) -> return_one (mkCharToken (SLoc (row1, col1) (row2, col2)) this)
            ((40, this), ((row1, col1), (row2, col2))) -> return []
            ((41, this), ((row1, col1), (row2, col2))) -> return []
            ((42, this), ((row1, col1), (row2, col2))) -> return []
        tokens2 <- runHolLexerRaw_this str1
        return (tokens1 ++ tokens2)
