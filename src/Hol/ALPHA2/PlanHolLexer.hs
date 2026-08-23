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
    tokens <- runHolLexerRaw src
    case [start | T_lex_error (SLoc start _) <- tokens] of
        start : _ -> Left start
        [] -> Right tokens

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
        { getInitialQOfDFA = 10
        , getFinalQsOfDFA = XMap.fromAscList [(11, 1), (12, 2), (13, 3), (14, 4), (15, 5), (16, 6), (17, 7), (18, 8), (19, 9), (20, 10), (21, 12), (22, 13), (23, 14), (24, 15), (25, 16), (26, 17), (27, 18), (28, 19), (29, 20), (30, 21), (31, 22), (32, 23), (33, 24), (34, 25), (35, 26), (36, 27), (37, 28), (38, 29), (39, 30), (40, 31), (41, 32), (42, 33), (43, 34), (44, 35), (45, 35), (46, 35), (47, 35), (48, 35), (49, 35), (50, 35), (51, 35), (52, 35), (53, 35), (54, 35), (55, 35), (56, 35), (57, 35), (58, 35), (59, 35), (60, 35), (61, 35), (62, 35), (63, 35), (64, 35), (65, 36), (66, 37), (67, 38), (68, 39), (69, 40), (70, 41)]
        , getTransitionsOfDFA = XMap.fromList
            [ ((1, Just '\t'), 1), ((1, Just '\n'), 1), ((1, Just '\r'), 1), ((1, Just ' '), 1), ((1, Just '!'), 1), ((1, Just '"'), 1), ((1, Just '%'), 1), ((1, Just '\''), 1), ((1, Just '('), 1), ((1, Just ')'), 1), ((1, Just '*'), 7), ((1, Just '+'), 1), ((1, Just ','), 1), ((1, Just '-'), 1), ((1, Just '.'), 1), ((1, Just '/'), 1), ((1, Just '0'), 1), ((1, Just '1'), 1), ((1, Just '2'), 1), ((1, Just '3'), 1), ((1, Just '4'), 1), ((1, Just '5'), 1), ((1, Just '6'), 1), ((1, Just '7'), 1), ((1, Just '8'), 1), ((1, Just '9'), 1), ((1, Just ':'), 1), ((1, Just ';'), 1), ((1, Just '<'), 1), ((1, Just '='), 1), ((1, Just '>'), 1), ((1, Just '?'), 1), ((1, Just 'A'), 1), ((1, Just 'B'), 1), ((1, Just 'C'), 1), ((1, Just 'D'), 1), ((1, Just 'E'), 1), ((1, Just 'F'), 1), ((1, Just 'G'), 1), ((1, Just 'H'), 1), ((1, Just 'I'), 1), ((1, Just 'J'), 1), ((1, Just 'K'), 1), ((1, Just 'L'), 1), ((1, Just 'M'), 1), ((1, Just 'N'), 1), ((1, Just 'O'), 1), ((1, Just 'P'), 1), ((1, Just 'Q'), 1), ((1, Just 'R'), 1), ((1, Just 'S'), 1), ((1, Just 'T'), 1), ((1, Just 'U'), 1), ((1, Just 'V'), 1), ((1, Just 'W'), 1), ((1, Just 'X'), 1), ((1, Just 'Y'), 1), ((1, Just 'Z'), 1), ((1, Just '['), 1), ((1, Just '\\'), 1), ((1, Just ']'), 1), ((1, Just '_'), 1), ((1, Just 'a'), 1), ((1, Just 'b'), 1), ((1, Just 'c'), 1), ((1, Just 'd'), 1), ((1, Just 'e'), 1), ((1, Just 'f'), 1), ((1, Just 'g'), 1), ((1, Just 'h'), 1), ((1, Just 'i'), 1), ((1, Just 'j'), 1), ((1, Just 'k'), 1), ((1, Just 'l'), 1), ((1, Just 'm'), 1), ((1, Just 'n'), 1), ((1, Just 'o'), 1), ((1, Just 'p'), 1), ((1, Just 'q'), 1), ((1, Just 'r'), 1), ((1, Just 's'), 1), ((1, Just 't'), 1), ((1, Just 'u'), 1), ((1, Just 'v'), 1), ((1, Just 'w'), 1), ((1, Just 'x'), 1), ((1, Just 'y'), 1), ((1, Just 'z'), 1), ((1, Nothing), 1)
            , ((2, Just '"'), 6), ((2, Just '\''), 6), ((2, Just '\\'), 6), ((2, Just 'n'), 6), ((2, Just 't'), 6)
            , ((3, Just '"'), 5), ((3, Just '\''), 5), ((3, Just '\\'), 5), ((3, Just 'n'), 5), ((3, Just 't'), 5)
            , ((4, Just '\t'), 6), ((4, Just '\r'), 6), ((4, Just ' '), 6), ((4, Just '!'), 6), ((4, Just '"'), 6), ((4, Just '%'), 6), ((4, Just '('), 6), ((4, Just ')'), 6), ((4, Just '*'), 6), ((4, Just '+'), 6), ((4, Just ','), 6), ((4, Just '-'), 6), ((4, Just '.'), 6), ((4, Just '/'), 6), ((4, Just '0'), 6), ((4, Just '1'), 6), ((4, Just '2'), 6), ((4, Just '3'), 6), ((4, Just '4'), 6), ((4, Just '5'), 6), ((4, Just '6'), 6), ((4, Just '7'), 6), ((4, Just '8'), 6), ((4, Just '9'), 6), ((4, Just ':'), 6), ((4, Just ';'), 6), ((4, Just '<'), 6), ((4, Just '='), 6), ((4, Just '>'), 6), ((4, Just '?'), 6), ((4, Just 'A'), 6), ((4, Just 'B'), 6), ((4, Just 'C'), 6), ((4, Just 'D'), 6), ((4, Just 'E'), 6), ((4, Just 'F'), 6), ((4, Just 'G'), 6), ((4, Just 'H'), 6), ((4, Just 'I'), 6), ((4, Just 'J'), 6), ((4, Just 'K'), 6), ((4, Just 'L'), 6), ((4, Just 'M'), 6), ((4, Just 'N'), 6), ((4, Just 'O'), 6), ((4, Just 'P'), 6), ((4, Just 'Q'), 6), ((4, Just 'R'), 6), ((4, Just 'S'), 6), ((4, Just 'T'), 6), ((4, Just 'U'), 6), ((4, Just 'V'), 6), ((4, Just 'W'), 6), ((4, Just 'X'), 6), ((4, Just 'Y'), 6), ((4, Just 'Z'), 6), ((4, Just '['), 6), ((4, Just '\\'), 2), ((4, Just ']'), 6), ((4, Just '_'), 6), ((4, Just 'a'), 6), ((4, Just 'b'), 6), ((4, Just 'c'), 6), ((4, Just 'd'), 6), ((4, Just 'e'), 6), ((4, Just 'f'), 6), ((4, Just 'g'), 6), ((4, Just 'h'), 6), ((4, Just 'i'), 6), ((4, Just 'j'), 6), ((4, Just 'k'), 6), ((4, Just 'l'), 6), ((4, Just 'm'), 6), ((4, Just 'n'), 6), ((4, Just 'o'), 6), ((4, Just 'p'), 6), ((4, Just 'q'), 6), ((4, Just 'r'), 6), ((4, Just 's'), 6), ((4, Just 't'), 6), ((4, Just 'u'), 6), ((4, Just 'v'), 6), ((4, Just 'w'), 6), ((4, Just 'x'), 6), ((4, Just 'y'), 6), ((4, Just 'z'), 6), ((4, Nothing), 6)
            , ((5, Just '\t'), 5), ((5, Just '\r'), 5), ((5, Just ' '), 5), ((5, Just '!'), 5), ((5, Just '"'), 66), ((5, Just '%'), 5), ((5, Just '\''), 5), ((5, Just '('), 5), ((5, Just ')'), 5), ((5, Just '*'), 5), ((5, Just '+'), 5), ((5, Just ','), 5), ((5, Just '-'), 5), ((5, Just '.'), 5), ((5, Just '/'), 5), ((5, Just '0'), 5), ((5, Just '1'), 5), ((5, Just '2'), 5), ((5, Just '3'), 5), ((5, Just '4'), 5), ((5, Just '5'), 5), ((5, Just '6'), 5), ((5, Just '7'), 5), ((5, Just '8'), 5), ((5, Just '9'), 5), ((5, Just ':'), 5), ((5, Just ';'), 5), ((5, Just '<'), 5), ((5, Just '='), 5), ((5, Just '>'), 5), ((5, Just '?'), 5), ((5, Just 'A'), 5), ((5, Just 'B'), 5), ((5, Just 'C'), 5), ((5, Just 'D'), 5), ((5, Just 'E'), 5), ((5, Just 'F'), 5), ((5, Just 'G'), 5), ((5, Just 'H'), 5), ((5, Just 'I'), 5), ((5, Just 'J'), 5), ((5, Just 'K'), 5), ((5, Just 'L'), 5), ((5, Just 'M'), 5), ((5, Just 'N'), 5), ((5, Just 'O'), 5), ((5, Just 'P'), 5), ((5, Just 'Q'), 5), ((5, Just 'R'), 5), ((5, Just 'S'), 5), ((5, Just 'T'), 5), ((5, Just 'U'), 5), ((5, Just 'V'), 5), ((5, Just 'W'), 5), ((5, Just 'X'), 5), ((5, Just 'Y'), 5), ((5, Just 'Z'), 5), ((5, Just '['), 5), ((5, Just '\\'), 3), ((5, Just ']'), 5), ((5, Just '_'), 5), ((5, Just 'a'), 5), ((5, Just 'b'), 5), ((5, Just 'c'), 5), ((5, Just 'd'), 5), ((5, Just 'e'), 5), ((5, Just 'f'), 5), ((5, Just 'g'), 5), ((5, Just 'h'), 5), ((5, Just 'i'), 5), ((5, Just 'j'), 5), ((5, Just 'k'), 5), ((5, Just 'l'), 5), ((5, Just 'm'), 5), ((5, Just 'n'), 5), ((5, Just 'o'), 5), ((5, Just 'p'), 5), ((5, Just 'q'), 5), ((5, Just 'r'), 5), ((5, Just 's'), 5), ((5, Just 't'), 5), ((5, Just 'u'), 5), ((5, Just 'v'), 5), ((5, Just 'w'), 5), ((5, Just 'x'), 5), ((5, Just 'y'), 5), ((5, Just 'z'), 5), ((5, Nothing), 5)
            , ((6, Just '\''), 67)
            , ((7, Just '\t'), 1), ((7, Just '\n'), 1), ((7, Just '\r'), 1), ((7, Just ' '), 1), ((7, Just '!'), 1), ((7, Just '"'), 1), ((7, Just '%'), 1), ((7, Just '\''), 1), ((7, Just '('), 1), ((7, Just ')'), 70), ((7, Just '*'), 1), ((7, Just '+'), 1), ((7, Just ','), 1), ((7, Just '-'), 1), ((7, Just '.'), 1), ((7, Just '/'), 1), ((7, Just '0'), 1), ((7, Just '1'), 1), ((7, Just '2'), 1), ((7, Just '3'), 1), ((7, Just '4'), 1), ((7, Just '5'), 1), ((7, Just '6'), 1), ((7, Just '7'), 1), ((7, Just '8'), 1), ((7, Just '9'), 1), ((7, Just ':'), 1), ((7, Just ';'), 1), ((7, Just '<'), 1), ((7, Just '='), 1), ((7, Just '>'), 1), ((7, Just '?'), 1), ((7, Just 'A'), 1), ((7, Just 'B'), 1), ((7, Just 'C'), 1), ((7, Just 'D'), 1), ((7, Just 'E'), 1), ((7, Just 'F'), 1), ((7, Just 'G'), 1), ((7, Just 'H'), 1), ((7, Just 'I'), 1), ((7, Just 'J'), 1), ((7, Just 'K'), 1), ((7, Just 'L'), 1), ((7, Just 'M'), 1), ((7, Just 'N'), 1), ((7, Just 'O'), 1), ((7, Just 'P'), 1), ((7, Just 'Q'), 1), ((7, Just 'R'), 1), ((7, Just 'S'), 1), ((7, Just 'T'), 1), ((7, Just 'U'), 1), ((7, Just 'V'), 1), ((7, Just 'W'), 1), ((7, Just 'X'), 1), ((7, Just 'Y'), 1), ((7, Just 'Z'), 1), ((7, Just '['), 1), ((7, Just '\\'), 1), ((7, Just ']'), 1), ((7, Just '_'), 1), ((7, Just 'a'), 1), ((7, Just 'b'), 1), ((7, Just 'c'), 1), ((7, Just 'd'), 1), ((7, Just 'e'), 1), ((7, Just 'f'), 1), ((7, Just 'g'), 1), ((7, Just 'h'), 1), ((7, Just 'i'), 1), ((7, Just 'j'), 1), ((7, Just 'k'), 1), ((7, Just 'l'), 1), ((7, Just 'm'), 1), ((7, Just 'n'), 1), ((7, Just 'o'), 1), ((7, Just 'p'), 1), ((7, Just 'q'), 1), ((7, Just 'r'), 1), ((7, Just 's'), 1), ((7, Just 't'), 1), ((7, Just 'u'), 1), ((7, Just 'v'), 1), ((7, Just 'w'), 1), ((7, Just 'x'), 1), ((7, Just 'y'), 1), ((7, Just 'z'), 1), ((7, Nothing), 1)
            , ((8, Just '-'), 19)
            , ((9, Just '-'), 21), ((9, Just ':'), 41)
            , ((10, Just '\t'), 68), ((10, Just '\n'), 68), ((10, Just '\r'), 68), ((10, Just ' '), 68), ((10, Just '!'), 35), ((10, Just '"'), 5), ((10, Just '%'), 69), ((10, Just '\''), 4), ((10, Just '('), 15), ((10, Just ')'), 16), ((10, Just '*'), 30), ((10, Just '+'), 28), ((10, Just ','), 20), ((10, Just '-'), 29), ((10, Just '.'), 12), ((10, Just '/'), 31), ((10, Just '0'), 65), ((10, Just '1'), 65), ((10, Just '2'), 65), ((10, Just '3'), 65), ((10, Just '4'), 65), ((10, Just '5'), 65), ((10, Just '6'), 65), ((10, Just '7'), 65), ((10, Just '8'), 65), ((10, Just '9'), 65), ((10, Just ':'), 9), ((10, Just ';'), 34), ((10, Just '<'), 25), ((10, Just '='), 23), ((10, Just '>'), 27), ((10, Just '?'), 8), ((10, Just 'A'), 57), ((10, Just 'B'), 57), ((10, Just 'C'), 57), ((10, Just 'D'), 57), ((10, Just 'E'), 57), ((10, Just 'F'), 57), ((10, Just 'G'), 57), ((10, Just 'H'), 57), ((10, Just 'I'), 57), ((10, Just 'J'), 57), ((10, Just 'K'), 57), ((10, Just 'L'), 57), ((10, Just 'M'), 57), ((10, Just 'N'), 57), ((10, Just 'O'), 57), ((10, Just 'P'), 57), ((10, Just 'Q'), 57), ((10, Just 'R'), 57), ((10, Just 'S'), 57), ((10, Just 'T'), 57), ((10, Just 'U'), 57), ((10, Just 'V'), 57), ((10, Just 'W'), 57), ((10, Just 'X'), 57), ((10, Just 'Y'), 57), ((10, Just 'Z'), 57), ((10, Just '['), 17), ((10, Just '\\'), 40), ((10, Just ']'), 18), ((10, Just '_'), 11), ((10, Just 'a'), 57), ((10, Just 'b'), 57), ((10, Just 'c'), 57), ((10, Just 'd'), 54), ((10, Just 'e'), 57), ((10, Just 'f'), 56), ((10, Just 'g'), 57), ((10, Just 'h'), 57), ((10, Just 'i'), 64), ((10, Just 'j'), 57), ((10, Just 'k'), 48), ((10, Just 'l'), 57), ((10, Just 'm'), 57), ((10, Just 'n'), 57), ((10, Just 'o'), 57), ((10, Just 'p'), 44), ((10, Just 'q'), 57), ((10, Just 'r'), 57), ((10, Just 's'), 22), ((10, Just 't'), 51), ((10, Just 'u'), 57), ((10, Just 'v'), 57), ((10, Just 'w'), 57), ((10, Just 'x'), 57), ((10, Just 'y'), 57), ((10, Just 'z'), 57)
            , ((15, Just '*'), 1)
            , ((22, Just '0'), 57), ((22, Just '1'), 57), ((22, Just '2'), 57), ((22, Just '3'), 57), ((22, Just '4'), 57), ((22, Just '5'), 57), ((22, Just '6'), 57), ((22, Just '7'), 57), ((22, Just '8'), 57), ((22, Just '9'), 57), ((22, Just 'A'), 57), ((22, Just 'B'), 57), ((22, Just 'C'), 57), ((22, Just 'D'), 57), ((22, Just 'E'), 57), ((22, Just 'F'), 57), ((22, Just 'G'), 57), ((22, Just 'H'), 57), ((22, Just 'I'), 57), ((22, Just 'J'), 57), ((22, Just 'K'), 57), ((22, Just 'L'), 57), ((22, Just 'M'), 57), ((22, Just 'N'), 57), ((22, Just 'O'), 57), ((22, Just 'P'), 57), ((22, Just 'Q'), 57), ((22, Just 'R'), 57), ((22, Just 'S'), 57), ((22, Just 'T'), 57), ((22, Just 'U'), 57), ((22, Just 'V'), 57), ((22, Just 'W'), 57), ((22, Just 'X'), 57), ((22, Just 'Y'), 57), ((22, Just 'Z'), 57), ((22, Just '_'), 57), ((22, Just 'a'), 57), ((22, Just 'b'), 57), ((22, Just 'c'), 57), ((22, Just 'd'), 57), ((22, Just 'e'), 57), ((22, Just 'f'), 57), ((22, Just 'g'), 57), ((22, Just 'h'), 57), ((22, Just 'i'), 46), ((22, Just 'j'), 57), ((22, Just 'k'), 57), ((22, Just 'l'), 57), ((22, Just 'm'), 57), ((22, Just 'n'), 57), ((22, Just 'o'), 57), ((22, Just 'p'), 57), ((22, Just 'q'), 57), ((22, Just 'r'), 57), ((22, Just 's'), 57), ((22, Just 't'), 57), ((22, Just 'u'), 57), ((22, Just 'v'), 57), ((22, Just 'w'), 57), ((22, Just 'x'), 57), ((22, Just 'y'), 57), ((22, Just 'z'), 57)
            , ((23, Just '<'), 24), ((23, Just '>'), 14)
            , ((27, Just '='), 26)
            , ((29, Just '>'), 13)
            , ((32, Just '0'), 57), ((32, Just '1'), 57), ((32, Just '2'), 57), ((32, Just '3'), 57), ((32, Just '4'), 57), ((32, Just '5'), 57), ((32, Just '6'), 57), ((32, Just '7'), 57), ((32, Just '8'), 57), ((32, Just '9'), 57), ((32, Just 'A'), 57), ((32, Just 'B'), 57), ((32, Just 'C'), 57), ((32, Just 'D'), 57), ((32, Just 'E'), 57), ((32, Just 'F'), 57), ((32, Just 'G'), 57), ((32, Just 'H'), 57), ((32, Just 'I'), 57), ((32, Just 'J'), 57), ((32, Just 'K'), 57), ((32, Just 'L'), 57), ((32, Just 'M'), 57), ((32, Just 'N'), 57), ((32, Just 'O'), 57), ((32, Just 'P'), 57), ((32, Just 'Q'), 57), ((32, Just 'R'), 57), ((32, Just 'S'), 57), ((32, Just 'T'), 57), ((32, Just 'U'), 57), ((32, Just 'V'), 57), ((32, Just 'W'), 57), ((32, Just 'X'), 57), ((32, Just 'Y'), 57), ((32, Just 'Z'), 57), ((32, Just '_'), 57), ((32, Just 'a'), 57), ((32, Just 'b'), 57), ((32, Just 'c'), 57), ((32, Just 'd'), 57), ((32, Just 'e'), 57), ((32, Just 'f'), 57), ((32, Just 'g'), 57), ((32, Just 'h'), 57), ((32, Just 'i'), 57), ((32, Just 'j'), 57), ((32, Just 'k'), 57), ((32, Just 'l'), 57), ((32, Just 'm'), 57), ((32, Just 'n'), 57), ((32, Just 'o'), 57), ((32, Just 'p'), 57), ((32, Just 'q'), 57), ((32, Just 'r'), 57), ((32, Just 's'), 57), ((32, Just 't'), 57), ((32, Just 'u'), 57), ((32, Just 'v'), 57), ((32, Just 'w'), 57), ((32, Just 'x'), 57), ((32, Just 'y'), 57), ((32, Just 'z'), 57)
            , ((33, Just '0'), 57), ((33, Just '1'), 57), ((33, Just '2'), 57), ((33, Just '3'), 57), ((33, Just '4'), 57), ((33, Just '5'), 57), ((33, Just '6'), 57), ((33, Just '7'), 57), ((33, Just '8'), 57), ((33, Just '9'), 57), ((33, Just 'A'), 57), ((33, Just 'B'), 57), ((33, Just 'C'), 57), ((33, Just 'D'), 57), ((33, Just 'E'), 57), ((33, Just 'F'), 57), ((33, Just 'G'), 57), ((33, Just 'H'), 57), ((33, Just 'I'), 57), ((33, Just 'J'), 57), ((33, Just 'K'), 57), ((33, Just 'L'), 57), ((33, Just 'M'), 57), ((33, Just 'N'), 57), ((33, Just 'O'), 57), ((33, Just 'P'), 57), ((33, Just 'Q'), 57), ((33, Just 'R'), 57), ((33, Just 'S'), 57), ((33, Just 'T'), 57), ((33, Just 'U'), 57), ((33, Just 'V'), 57), ((33, Just 'W'), 57), ((33, Just 'X'), 57), ((33, Just 'Y'), 57), ((33, Just 'Z'), 57), ((33, Just '_'), 57), ((33, Just 'a'), 57), ((33, Just 'b'), 57), ((33, Just 'c'), 57), ((33, Just 'd'), 57), ((33, Just 'e'), 57), ((33, Just 'f'), 57), ((33, Just 'g'), 57), ((33, Just 'h'), 57), ((33, Just 'i'), 57), ((33, Just 'j'), 57), ((33, Just 'k'), 57), ((33, Just 'l'), 57), ((33, Just 'm'), 57), ((33, Just 'n'), 57), ((33, Just 'o'), 57), ((33, Just 'p'), 57), ((33, Just 'q'), 57), ((33, Just 'r'), 57), ((33, Just 's'), 57), ((33, Just 't'), 57), ((33, Just 'u'), 57), ((33, Just 'v'), 57), ((33, Just 'w'), 57), ((33, Just 'x'), 57), ((33, Just 'y'), 57), ((33, Just 'z'), 57)
            , ((36, Just '0'), 57), ((36, Just '1'), 57), ((36, Just '2'), 57), ((36, Just '3'), 57), ((36, Just '4'), 57), ((36, Just '5'), 57), ((36, Just '6'), 57), ((36, Just '7'), 57), ((36, Just '8'), 57), ((36, Just '9'), 57), ((36, Just 'A'), 57), ((36, Just 'B'), 57), ((36, Just 'C'), 57), ((36, Just 'D'), 57), ((36, Just 'E'), 57), ((36, Just 'F'), 57), ((36, Just 'G'), 57), ((36, Just 'H'), 57), ((36, Just 'I'), 57), ((36, Just 'J'), 57), ((36, Just 'K'), 57), ((36, Just 'L'), 57), ((36, Just 'M'), 57), ((36, Just 'N'), 57), ((36, Just 'O'), 57), ((36, Just 'P'), 57), ((36, Just 'Q'), 57), ((36, Just 'R'), 57), ((36, Just 'S'), 57), ((36, Just 'T'), 57), ((36, Just 'U'), 57), ((36, Just 'V'), 57), ((36, Just 'W'), 57), ((36, Just 'X'), 57), ((36, Just 'Y'), 57), ((36, Just 'Z'), 57), ((36, Just '_'), 57), ((36, Just 'a'), 57), ((36, Just 'b'), 57), ((36, Just 'c'), 57), ((36, Just 'd'), 57), ((36, Just 'e'), 57), ((36, Just 'f'), 57), ((36, Just 'g'), 57), ((36, Just 'h'), 57), ((36, Just 'i'), 57), ((36, Just 'j'), 57), ((36, Just 'k'), 57), ((36, Just 'l'), 57), ((36, Just 'm'), 57), ((36, Just 'n'), 57), ((36, Just 'o'), 57), ((36, Just 'p'), 57), ((36, Just 'q'), 57), ((36, Just 'r'), 57), ((36, Just 's'), 57), ((36, Just 't'), 57), ((36, Just 'u'), 57), ((36, Just 'v'), 57), ((36, Just 'w'), 57), ((36, Just 'x'), 57), ((36, Just 'y'), 57), ((36, Just 'z'), 57)
            , ((37, Just '0'), 57), ((37, Just '1'), 57), ((37, Just '2'), 57), ((37, Just '3'), 57), ((37, Just '4'), 57), ((37, Just '5'), 57), ((37, Just '6'), 57), ((37, Just '7'), 57), ((37, Just '8'), 57), ((37, Just '9'), 57), ((37, Just 'A'), 57), ((37, Just 'B'), 57), ((37, Just 'C'), 57), ((37, Just 'D'), 57), ((37, Just 'E'), 57), ((37, Just 'F'), 57), ((37, Just 'G'), 57), ((37, Just 'H'), 57), ((37, Just 'I'), 57), ((37, Just 'J'), 57), ((37, Just 'K'), 57), ((37, Just 'L'), 57), ((37, Just 'M'), 57), ((37, Just 'N'), 57), ((37, Just 'O'), 57), ((37, Just 'P'), 57), ((37, Just 'Q'), 57), ((37, Just 'R'), 57), ((37, Just 'S'), 57), ((37, Just 'T'), 57), ((37, Just 'U'), 57), ((37, Just 'V'), 57), ((37, Just 'W'), 57), ((37, Just 'X'), 57), ((37, Just 'Y'), 57), ((37, Just 'Z'), 57), ((37, Just '_'), 57), ((37, Just 'a'), 57), ((37, Just 'b'), 57), ((37, Just 'c'), 57), ((37, Just 'd'), 57), ((37, Just 'e'), 57), ((37, Just 'f'), 57), ((37, Just 'g'), 57), ((37, Just 'h'), 57), ((37, Just 'i'), 57), ((37, Just 'j'), 57), ((37, Just 'k'), 57), ((37, Just 'l'), 57), ((37, Just 'm'), 57), ((37, Just 'n'), 57), ((37, Just 'o'), 57), ((37, Just 'p'), 57), ((37, Just 'q'), 57), ((37, Just 'r'), 57), ((37, Just 's'), 57), ((37, Just 't'), 57), ((37, Just 'u'), 57), ((37, Just 'v'), 57), ((37, Just 'w'), 57), ((37, Just 'x'), 57), ((37, Just 'y'), 57), ((37, Just 'z'), 57)
            , ((38, Just '0'), 57), ((38, Just '1'), 57), ((38, Just '2'), 57), ((38, Just '3'), 57), ((38, Just '4'), 57), ((38, Just '5'), 57), ((38, Just '6'), 57), ((38, Just '7'), 57), ((38, Just '8'), 57), ((38, Just '9'), 57), ((38, Just 'A'), 57), ((38, Just 'B'), 57), ((38, Just 'C'), 57), ((38, Just 'D'), 57), ((38, Just 'E'), 57), ((38, Just 'F'), 57), ((38, Just 'G'), 57), ((38, Just 'H'), 57), ((38, Just 'I'), 57), ((38, Just 'J'), 57), ((38, Just 'K'), 57), ((38, Just 'L'), 57), ((38, Just 'M'), 57), ((38, Just 'N'), 57), ((38, Just 'O'), 57), ((38, Just 'P'), 57), ((38, Just 'Q'), 57), ((38, Just 'R'), 57), ((38, Just 'S'), 57), ((38, Just 'T'), 57), ((38, Just 'U'), 57), ((38, Just 'V'), 57), ((38, Just 'W'), 57), ((38, Just 'X'), 57), ((38, Just 'Y'), 57), ((38, Just 'Z'), 57), ((38, Just '_'), 57), ((38, Just 'a'), 57), ((38, Just 'b'), 57), ((38, Just 'c'), 57), ((38, Just 'd'), 57), ((38, Just 'e'), 57), ((38, Just 'f'), 57), ((38, Just 'g'), 57), ((38, Just 'h'), 57), ((38, Just 'i'), 57), ((38, Just 'j'), 57), ((38, Just 'k'), 57), ((38, Just 'l'), 57), ((38, Just 'm'), 57), ((38, Just 'n'), 57), ((38, Just 'o'), 57), ((38, Just 'p'), 57), ((38, Just 'q'), 57), ((38, Just 'r'), 57), ((38, Just 's'), 57), ((38, Just 't'), 57), ((38, Just 'u'), 57), ((38, Just 'v'), 57), ((38, Just 'w'), 57), ((38, Just 'x'), 57), ((38, Just 'y'), 57), ((38, Just 'z'), 57)
            , ((39, Just '0'), 57), ((39, Just '1'), 57), ((39, Just '2'), 57), ((39, Just '3'), 57), ((39, Just '4'), 57), ((39, Just '5'), 57), ((39, Just '6'), 57), ((39, Just '7'), 57), ((39, Just '8'), 57), ((39, Just '9'), 57), ((39, Just 'A'), 57), ((39, Just 'B'), 57), ((39, Just 'C'), 57), ((39, Just 'D'), 57), ((39, Just 'E'), 57), ((39, Just 'F'), 57), ((39, Just 'G'), 57), ((39, Just 'H'), 57), ((39, Just 'I'), 57), ((39, Just 'J'), 57), ((39, Just 'K'), 57), ((39, Just 'L'), 57), ((39, Just 'M'), 57), ((39, Just 'N'), 57), ((39, Just 'O'), 57), ((39, Just 'P'), 57), ((39, Just 'Q'), 57), ((39, Just 'R'), 57), ((39, Just 'S'), 57), ((39, Just 'T'), 57), ((39, Just 'U'), 57), ((39, Just 'V'), 57), ((39, Just 'W'), 57), ((39, Just 'X'), 57), ((39, Just 'Y'), 57), ((39, Just 'Z'), 57), ((39, Just '_'), 57), ((39, Just 'a'), 57), ((39, Just 'b'), 57), ((39, Just 'c'), 57), ((39, Just 'd'), 57), ((39, Just 'e'), 57), ((39, Just 'f'), 57), ((39, Just 'g'), 57), ((39, Just 'h'), 57), ((39, Just 'i'), 57), ((39, Just 'j'), 57), ((39, Just 'k'), 57), ((39, Just 'l'), 57), ((39, Just 'm'), 57), ((39, Just 'n'), 57), ((39, Just 'o'), 57), ((39, Just 'p'), 57), ((39, Just 'q'), 57), ((39, Just 'r'), 57), ((39, Just 's'), 57), ((39, Just 't'), 57), ((39, Just 'u'), 57), ((39, Just 'v'), 57), ((39, Just 'w'), 57), ((39, Just 'x'), 57), ((39, Just 'y'), 57), ((39, Just 'z'), 57)
            , ((42, Just '0'), 57), ((42, Just '1'), 57), ((42, Just '2'), 57), ((42, Just '3'), 57), ((42, Just '4'), 57), ((42, Just '5'), 57), ((42, Just '6'), 57), ((42, Just '7'), 57), ((42, Just '8'), 57), ((42, Just '9'), 57), ((42, Just 'A'), 57), ((42, Just 'B'), 57), ((42, Just 'C'), 57), ((42, Just 'D'), 57), ((42, Just 'E'), 57), ((42, Just 'F'), 57), ((42, Just 'G'), 57), ((42, Just 'H'), 57), ((42, Just 'I'), 57), ((42, Just 'J'), 57), ((42, Just 'K'), 57), ((42, Just 'L'), 57), ((42, Just 'M'), 57), ((42, Just 'N'), 57), ((42, Just 'O'), 57), ((42, Just 'P'), 57), ((42, Just 'Q'), 57), ((42, Just 'R'), 57), ((42, Just 'S'), 57), ((42, Just 'T'), 57), ((42, Just 'U'), 57), ((42, Just 'V'), 57), ((42, Just 'W'), 57), ((42, Just 'X'), 57), ((42, Just 'Y'), 57), ((42, Just 'Z'), 57), ((42, Just '_'), 57), ((42, Just 'a'), 57), ((42, Just 'b'), 57), ((42, Just 'c'), 57), ((42, Just 'd'), 57), ((42, Just 'e'), 57), ((42, Just 'f'), 57), ((42, Just 'g'), 57), ((42, Just 'h'), 57), ((42, Just 'i'), 57), ((42, Just 'j'), 57), ((42, Just 'k'), 57), ((42, Just 'l'), 57), ((42, Just 'm'), 57), ((42, Just 'n'), 57), ((42, Just 'o'), 57), ((42, Just 'p'), 57), ((42, Just 'q'), 57), ((42, Just 'r'), 57), ((42, Just 's'), 57), ((42, Just 't'), 57), ((42, Just 'u'), 57), ((42, Just 'v'), 57), ((42, Just 'w'), 57), ((42, Just 'x'), 57), ((42, Just 'y'), 57), ((42, Just 'z'), 57)
            , ((43, Just '0'), 57), ((43, Just '1'), 57), ((43, Just '2'), 57), ((43, Just '3'), 57), ((43, Just '4'), 57), ((43, Just '5'), 57), ((43, Just '6'), 57), ((43, Just '7'), 57), ((43, Just '8'), 57), ((43, Just '9'), 57), ((43, Just 'A'), 57), ((43, Just 'B'), 57), ((43, Just 'C'), 57), ((43, Just 'D'), 57), ((43, Just 'E'), 57), ((43, Just 'F'), 57), ((43, Just 'G'), 57), ((43, Just 'H'), 57), ((43, Just 'I'), 57), ((43, Just 'J'), 57), ((43, Just 'K'), 57), ((43, Just 'L'), 57), ((43, Just 'M'), 57), ((43, Just 'N'), 57), ((43, Just 'O'), 57), ((43, Just 'P'), 57), ((43, Just 'Q'), 57), ((43, Just 'R'), 57), ((43, Just 'S'), 57), ((43, Just 'T'), 57), ((43, Just 'U'), 57), ((43, Just 'V'), 57), ((43, Just 'W'), 57), ((43, Just 'X'), 57), ((43, Just 'Y'), 57), ((43, Just 'Z'), 57), ((43, Just '_'), 57), ((43, Just 'a'), 57), ((43, Just 'b'), 57), ((43, Just 'c'), 57), ((43, Just 'd'), 57), ((43, Just 'e'), 57), ((43, Just 'f'), 57), ((43, Just 'g'), 57), ((43, Just 'h'), 57), ((43, Just 'i'), 57), ((43, Just 'j'), 57), ((43, Just 'k'), 57), ((43, Just 'l'), 57), ((43, Just 'm'), 57), ((43, Just 'n'), 57), ((43, Just 'o'), 57), ((43, Just 'p'), 57), ((43, Just 'q'), 57), ((43, Just 'r'), 57), ((43, Just 's'), 57), ((43, Just 't'), 57), ((43, Just 'u'), 57), ((43, Just 'v'), 57), ((43, Just 'w'), 57), ((43, Just 'x'), 57), ((43, Just 'y'), 57), ((43, Just 'z'), 57)
            , ((44, Just '0'), 57), ((44, Just '1'), 57), ((44, Just '2'), 57), ((44, Just '3'), 57), ((44, Just '4'), 57), ((44, Just '5'), 57), ((44, Just '6'), 57), ((44, Just '7'), 57), ((44, Just '8'), 57), ((44, Just '9'), 57), ((44, Just 'A'), 57), ((44, Just 'B'), 57), ((44, Just 'C'), 57), ((44, Just 'D'), 57), ((44, Just 'E'), 57), ((44, Just 'F'), 57), ((44, Just 'G'), 57), ((44, Just 'H'), 57), ((44, Just 'I'), 57), ((44, Just 'J'), 57), ((44, Just 'K'), 57), ((44, Just 'L'), 57), ((44, Just 'M'), 57), ((44, Just 'N'), 57), ((44, Just 'O'), 57), ((44, Just 'P'), 57), ((44, Just 'Q'), 57), ((44, Just 'R'), 57), ((44, Just 'S'), 57), ((44, Just 'T'), 57), ((44, Just 'U'), 57), ((44, Just 'V'), 57), ((44, Just 'W'), 57), ((44, Just 'X'), 57), ((44, Just 'Y'), 57), ((44, Just 'Z'), 57), ((44, Just '_'), 57), ((44, Just 'a'), 57), ((44, Just 'b'), 57), ((44, Just 'c'), 57), ((44, Just 'd'), 57), ((44, Just 'e'), 57), ((44, Just 'f'), 57), ((44, Just 'g'), 57), ((44, Just 'h'), 57), ((44, Just 'i'), 32), ((44, Just 'j'), 57), ((44, Just 'k'), 57), ((44, Just 'l'), 57), ((44, Just 'm'), 57), ((44, Just 'n'), 57), ((44, Just 'o'), 57), ((44, Just 'p'), 57), ((44, Just 'q'), 57), ((44, Just 'r'), 57), ((44, Just 's'), 57), ((44, Just 't'), 57), ((44, Just 'u'), 57), ((44, Just 'v'), 57), ((44, Just 'w'), 57), ((44, Just 'x'), 57), ((44, Just 'y'), 57), ((44, Just 'z'), 57)
            , ((45, Just '0'), 57), ((45, Just '1'), 57), ((45, Just '2'), 57), ((45, Just '3'), 57), ((45, Just '4'), 57), ((45, Just '5'), 57), ((45, Just '6'), 57), ((45, Just '7'), 57), ((45, Just '8'), 57), ((45, Just '9'), 57), ((45, Just 'A'), 57), ((45, Just 'B'), 57), ((45, Just 'C'), 57), ((45, Just 'D'), 57), ((45, Just 'E'), 57), ((45, Just 'F'), 57), ((45, Just 'G'), 57), ((45, Just 'H'), 57), ((45, Just 'I'), 57), ((45, Just 'J'), 57), ((45, Just 'K'), 57), ((45, Just 'L'), 57), ((45, Just 'M'), 57), ((45, Just 'N'), 57), ((45, Just 'O'), 57), ((45, Just 'P'), 57), ((45, Just 'Q'), 57), ((45, Just 'R'), 57), ((45, Just 'S'), 57), ((45, Just 'T'), 57), ((45, Just 'U'), 57), ((45, Just 'V'), 57), ((45, Just 'W'), 57), ((45, Just 'X'), 57), ((45, Just 'Y'), 57), ((45, Just 'Z'), 57), ((45, Just '_'), 57), ((45, Just 'a'), 57), ((45, Just 'b'), 57), ((45, Just 'c'), 57), ((45, Just 'd'), 57), ((45, Just 'e'), 57), ((45, Just 'f'), 57), ((45, Just 'g'), 57), ((45, Just 'h'), 57), ((45, Just 'i'), 57), ((45, Just 'j'), 57), ((45, Just 'k'), 57), ((45, Just 'l'), 57), ((45, Just 'm'), 58), ((45, Just 'n'), 57), ((45, Just 'o'), 57), ((45, Just 'p'), 57), ((45, Just 'q'), 57), ((45, Just 'r'), 57), ((45, Just 's'), 57), ((45, Just 't'), 57), ((45, Just 'u'), 57), ((45, Just 'v'), 57), ((45, Just 'w'), 57), ((45, Just 'x'), 57), ((45, Just 'y'), 57), ((45, Just 'z'), 57)
            , ((46, Just '0'), 57), ((46, Just '1'), 57), ((46, Just '2'), 57), ((46, Just '3'), 57), ((46, Just '4'), 57), ((46, Just '5'), 57), ((46, Just '6'), 57), ((46, Just '7'), 57), ((46, Just '8'), 57), ((46, Just '9'), 57), ((46, Just 'A'), 57), ((46, Just 'B'), 57), ((46, Just 'C'), 57), ((46, Just 'D'), 57), ((46, Just 'E'), 57), ((46, Just 'F'), 57), ((46, Just 'G'), 57), ((46, Just 'H'), 57), ((46, Just 'I'), 57), ((46, Just 'J'), 57), ((46, Just 'K'), 57), ((46, Just 'L'), 57), ((46, Just 'M'), 57), ((46, Just 'N'), 57), ((46, Just 'O'), 57), ((46, Just 'P'), 57), ((46, Just 'Q'), 57), ((46, Just 'R'), 57), ((46, Just 'S'), 57), ((46, Just 'T'), 57), ((46, Just 'U'), 57), ((46, Just 'V'), 57), ((46, Just 'W'), 57), ((46, Just 'X'), 57), ((46, Just 'Y'), 57), ((46, Just 'Z'), 57), ((46, Just '_'), 57), ((46, Just 'a'), 57), ((46, Just 'b'), 57), ((46, Just 'c'), 57), ((46, Just 'd'), 57), ((46, Just 'e'), 57), ((46, Just 'f'), 57), ((46, Just 'g'), 45), ((46, Just 'h'), 57), ((46, Just 'i'), 57), ((46, Just 'j'), 57), ((46, Just 'k'), 57), ((46, Just 'l'), 57), ((46, Just 'm'), 57), ((46, Just 'n'), 57), ((46, Just 'o'), 57), ((46, Just 'p'), 57), ((46, Just 'q'), 57), ((46, Just 'r'), 57), ((46, Just 's'), 57), ((46, Just 't'), 57), ((46, Just 'u'), 57), ((46, Just 'v'), 57), ((46, Just 'w'), 57), ((46, Just 'x'), 57), ((46, Just 'y'), 57), ((46, Just 'z'), 57)
            , ((47, Just '0'), 57), ((47, Just '1'), 57), ((47, Just '2'), 57), ((47, Just '3'), 57), ((47, Just '4'), 57), ((47, Just '5'), 57), ((47, Just '6'), 57), ((47, Just '7'), 57), ((47, Just '8'), 57), ((47, Just '9'), 57), ((47, Just 'A'), 57), ((47, Just 'B'), 57), ((47, Just 'C'), 57), ((47, Just 'D'), 57), ((47, Just 'E'), 57), ((47, Just 'F'), 57), ((47, Just 'G'), 57), ((47, Just 'H'), 57), ((47, Just 'I'), 57), ((47, Just 'J'), 57), ((47, Just 'K'), 57), ((47, Just 'L'), 57), ((47, Just 'M'), 57), ((47, Just 'N'), 57), ((47, Just 'O'), 57), ((47, Just 'P'), 57), ((47, Just 'Q'), 57), ((47, Just 'R'), 57), ((47, Just 'S'), 57), ((47, Just 'T'), 57), ((47, Just 'U'), 57), ((47, Just 'V'), 57), ((47, Just 'W'), 57), ((47, Just 'X'), 57), ((47, Just 'Y'), 57), ((47, Just 'Z'), 57), ((47, Just '_'), 57), ((47, Just 'a'), 57), ((47, Just 'b'), 57), ((47, Just 'c'), 57), ((47, Just 'd'), 57), ((47, Just 'e'), 57), ((47, Just 'f'), 57), ((47, Just 'g'), 57), ((47, Just 'h'), 57), ((47, Just 'i'), 57), ((47, Just 'j'), 57), ((47, Just 'k'), 57), ((47, Just 'l'), 57), ((47, Just 'm'), 57), ((47, Just 'n'), 59), ((47, Just 'o'), 57), ((47, Just 'p'), 57), ((47, Just 'q'), 57), ((47, Just 'r'), 57), ((47, Just 's'), 57), ((47, Just 't'), 57), ((47, Just 'u'), 57), ((47, Just 'v'), 57), ((47, Just 'w'), 57), ((47, Just 'x'), 57), ((47, Just 'y'), 57), ((47, Just 'z'), 57)
            , ((48, Just '0'), 57), ((48, Just '1'), 57), ((48, Just '2'), 57), ((48, Just '3'), 57), ((48, Just '4'), 57), ((48, Just '5'), 57), ((48, Just '6'), 57), ((48, Just '7'), 57), ((48, Just '8'), 57), ((48, Just '9'), 57), ((48, Just 'A'), 57), ((48, Just 'B'), 57), ((48, Just 'C'), 57), ((48, Just 'D'), 57), ((48, Just 'E'), 57), ((48, Just 'F'), 57), ((48, Just 'G'), 57), ((48, Just 'H'), 57), ((48, Just 'I'), 57), ((48, Just 'J'), 57), ((48, Just 'K'), 57), ((48, Just 'L'), 57), ((48, Just 'M'), 57), ((48, Just 'N'), 57), ((48, Just 'O'), 57), ((48, Just 'P'), 57), ((48, Just 'Q'), 57), ((48, Just 'R'), 57), ((48, Just 'S'), 57), ((48, Just 'T'), 57), ((48, Just 'U'), 57), ((48, Just 'V'), 57), ((48, Just 'W'), 57), ((48, Just 'X'), 57), ((48, Just 'Y'), 57), ((48, Just 'Z'), 57), ((48, Just '_'), 57), ((48, Just 'a'), 57), ((48, Just 'b'), 57), ((48, Just 'c'), 57), ((48, Just 'd'), 57), ((48, Just 'e'), 57), ((48, Just 'f'), 57), ((48, Just 'g'), 57), ((48, Just 'h'), 57), ((48, Just 'i'), 47), ((48, Just 'j'), 57), ((48, Just 'k'), 57), ((48, Just 'l'), 57), ((48, Just 'm'), 57), ((48, Just 'n'), 57), ((48, Just 'o'), 57), ((48, Just 'p'), 57), ((48, Just 'q'), 57), ((48, Just 'r'), 57), ((48, Just 's'), 57), ((48, Just 't'), 57), ((48, Just 'u'), 57), ((48, Just 'v'), 57), ((48, Just 'w'), 57), ((48, Just 'x'), 57), ((48, Just 'y'), 57), ((48, Just 'z'), 57)
            , ((49, Just '0'), 57), ((49, Just '1'), 57), ((49, Just '2'), 57), ((49, Just '3'), 57), ((49, Just '4'), 57), ((49, Just '5'), 57), ((49, Just '6'), 57), ((49, Just '7'), 57), ((49, Just '8'), 57), ((49, Just '9'), 57), ((49, Just 'A'), 57), ((49, Just 'B'), 57), ((49, Just 'C'), 57), ((49, Just 'D'), 57), ((49, Just 'E'), 57), ((49, Just 'F'), 57), ((49, Just 'G'), 57), ((49, Just 'H'), 57), ((49, Just 'I'), 57), ((49, Just 'J'), 57), ((49, Just 'K'), 57), ((49, Just 'L'), 57), ((49, Just 'M'), 57), ((49, Just 'N'), 57), ((49, Just 'O'), 57), ((49, Just 'P'), 57), ((49, Just 'Q'), 57), ((49, Just 'R'), 57), ((49, Just 'S'), 57), ((49, Just 'T'), 57), ((49, Just 'U'), 57), ((49, Just 'V'), 57), ((49, Just 'W'), 57), ((49, Just 'X'), 57), ((49, Just 'Y'), 57), ((49, Just 'Z'), 57), ((49, Just '_'), 57), ((49, Just 'a'), 57), ((49, Just 'b'), 57), ((49, Just 'c'), 57), ((49, Just 'd'), 57), ((49, Just 'e'), 57), ((49, Just 'f'), 57), ((49, Just 'g'), 57), ((49, Just 'h'), 57), ((49, Just 'i'), 57), ((49, Just 'j'), 57), ((49, Just 'k'), 57), ((49, Just 'l'), 57), ((49, Just 'm'), 57), ((49, Just 'n'), 57), ((49, Just 'o'), 57), ((49, Just 'p'), 57), ((49, Just 'q'), 57), ((49, Just 'r'), 57), ((49, Just 's'), 57), ((49, Just 't'), 57), ((49, Just 'u'), 60), ((49, Just 'v'), 57), ((49, Just 'w'), 57), ((49, Just 'x'), 57), ((49, Just 'y'), 57), ((49, Just 'z'), 57)
            , ((50, Just '0'), 57), ((50, Just '1'), 57), ((50, Just '2'), 57), ((50, Just '3'), 57), ((50, Just '4'), 57), ((50, Just '5'), 57), ((50, Just '6'), 57), ((50, Just '7'), 57), ((50, Just '8'), 57), ((50, Just '9'), 57), ((50, Just 'A'), 57), ((50, Just 'B'), 57), ((50, Just 'C'), 57), ((50, Just 'D'), 57), ((50, Just 'E'), 57), ((50, Just 'F'), 57), ((50, Just 'G'), 57), ((50, Just 'H'), 57), ((50, Just 'I'), 57), ((50, Just 'J'), 57), ((50, Just 'K'), 57), ((50, Just 'L'), 57), ((50, Just 'M'), 57), ((50, Just 'N'), 57), ((50, Just 'O'), 57), ((50, Just 'P'), 57), ((50, Just 'Q'), 57), ((50, Just 'R'), 57), ((50, Just 'S'), 57), ((50, Just 'T'), 57), ((50, Just 'U'), 57), ((50, Just 'V'), 57), ((50, Just 'W'), 57), ((50, Just 'X'), 57), ((50, Just 'Y'), 57), ((50, Just 'Z'), 57), ((50, Just '_'), 57), ((50, Just 'a'), 57), ((50, Just 'b'), 57), ((50, Just 'c'), 57), ((50, Just 'd'), 57), ((50, Just 'e'), 57), ((50, Just 'f'), 57), ((50, Just 'g'), 57), ((50, Just 'h'), 57), ((50, Just 'i'), 57), ((50, Just 'j'), 57), ((50, Just 'k'), 57), ((50, Just 'l'), 57), ((50, Just 'm'), 57), ((50, Just 'n'), 57), ((50, Just 'o'), 57), ((50, Just 'p'), 61), ((50, Just 'q'), 57), ((50, Just 'r'), 57), ((50, Just 's'), 57), ((50, Just 't'), 57), ((50, Just 'u'), 57), ((50, Just 'v'), 57), ((50, Just 'w'), 57), ((50, Just 'x'), 57), ((50, Just 'y'), 57), ((50, Just 'z'), 57)
            , ((51, Just '0'), 57), ((51, Just '1'), 57), ((51, Just '2'), 57), ((51, Just '3'), 57), ((51, Just '4'), 57), ((51, Just '5'), 57), ((51, Just '6'), 57), ((51, Just '7'), 57), ((51, Just '8'), 57), ((51, Just '9'), 57), ((51, Just 'A'), 57), ((51, Just 'B'), 57), ((51, Just 'C'), 57), ((51, Just 'D'), 57), ((51, Just 'E'), 57), ((51, Just 'F'), 57), ((51, Just 'G'), 57), ((51, Just 'H'), 57), ((51, Just 'I'), 57), ((51, Just 'J'), 57), ((51, Just 'K'), 57), ((51, Just 'L'), 57), ((51, Just 'M'), 57), ((51, Just 'N'), 57), ((51, Just 'O'), 57), ((51, Just 'P'), 57), ((51, Just 'Q'), 57), ((51, Just 'R'), 57), ((51, Just 'S'), 57), ((51, Just 'T'), 57), ((51, Just 'U'), 57), ((51, Just 'V'), 57), ((51, Just 'W'), 57), ((51, Just 'X'), 57), ((51, Just 'Y'), 57), ((51, Just 'Z'), 57), ((51, Just '_'), 57), ((51, Just 'a'), 57), ((51, Just 'b'), 57), ((51, Just 'c'), 57), ((51, Just 'd'), 57), ((51, Just 'e'), 57), ((51, Just 'f'), 57), ((51, Just 'g'), 57), ((51, Just 'h'), 57), ((51, Just 'i'), 57), ((51, Just 'j'), 57), ((51, Just 'k'), 57), ((51, Just 'l'), 57), ((51, Just 'm'), 57), ((51, Just 'n'), 57), ((51, Just 'o'), 57), ((51, Just 'p'), 57), ((51, Just 'q'), 57), ((51, Just 'r'), 49), ((51, Just 's'), 57), ((51, Just 't'), 57), ((51, Just 'u'), 57), ((51, Just 'v'), 57), ((51, Just 'w'), 57), ((51, Just 'x'), 57), ((51, Just 'y'), 50), ((51, Just 'z'), 57)
            , ((52, Just '0'), 57), ((52, Just '1'), 57), ((52, Just '2'), 57), ((52, Just '3'), 57), ((52, Just '4'), 57), ((52, Just '5'), 57), ((52, Just '6'), 57), ((52, Just '7'), 57), ((52, Just '8'), 57), ((52, Just '9'), 57), ((52, Just 'A'), 57), ((52, Just 'B'), 57), ((52, Just 'C'), 57), ((52, Just 'D'), 57), ((52, Just 'E'), 57), ((52, Just 'F'), 57), ((52, Just 'G'), 57), ((52, Just 'H'), 57), ((52, Just 'I'), 57), ((52, Just 'J'), 57), ((52, Just 'K'), 57), ((52, Just 'L'), 57), ((52, Just 'M'), 57), ((52, Just 'N'), 57), ((52, Just 'O'), 57), ((52, Just 'P'), 57), ((52, Just 'Q'), 57), ((52, Just 'R'), 57), ((52, Just 'S'), 57), ((52, Just 'T'), 57), ((52, Just 'U'), 57), ((52, Just 'V'), 57), ((52, Just 'W'), 57), ((52, Just 'X'), 57), ((52, Just 'Y'), 57), ((52, Just 'Z'), 57), ((52, Just '_'), 57), ((52, Just 'a'), 57), ((52, Just 'b'), 57), ((52, Just 'c'), 57), ((52, Just 'd'), 57), ((52, Just 'e'), 57), ((52, Just 'f'), 57), ((52, Just 'g'), 57), ((52, Just 'h'), 57), ((52, Just 'i'), 57), ((52, Just 'j'), 57), ((52, Just 'k'), 57), ((52, Just 'l'), 57), ((52, Just 'm'), 57), ((52, Just 'n'), 57), ((52, Just 'o'), 57), ((52, Just 'p'), 57), ((52, Just 'q'), 57), ((52, Just 'r'), 57), ((52, Just 's'), 57), ((52, Just 't'), 57), ((52, Just 'u'), 62), ((52, Just 'v'), 57), ((52, Just 'w'), 57), ((52, Just 'x'), 57), ((52, Just 'y'), 57), ((52, Just 'z'), 57)
            , ((53, Just '0'), 57), ((53, Just '1'), 57), ((53, Just '2'), 57), ((53, Just '3'), 57), ((53, Just '4'), 57), ((53, Just '5'), 57), ((53, Just '6'), 57), ((53, Just '7'), 57), ((53, Just '8'), 57), ((53, Just '9'), 57), ((53, Just 'A'), 57), ((53, Just 'B'), 57), ((53, Just 'C'), 57), ((53, Just 'D'), 57), ((53, Just 'E'), 57), ((53, Just 'F'), 57), ((53, Just 'G'), 57), ((53, Just 'H'), 57), ((53, Just 'I'), 57), ((53, Just 'J'), 57), ((53, Just 'K'), 57), ((53, Just 'L'), 57), ((53, Just 'M'), 57), ((53, Just 'N'), 57), ((53, Just 'O'), 57), ((53, Just 'P'), 57), ((53, Just 'Q'), 57), ((53, Just 'R'), 57), ((53, Just 'S'), 57), ((53, Just 'T'), 57), ((53, Just 'U'), 57), ((53, Just 'V'), 57), ((53, Just 'W'), 57), ((53, Just 'X'), 57), ((53, Just 'Y'), 57), ((53, Just 'Z'), 57), ((53, Just '_'), 57), ((53, Just 'a'), 57), ((53, Just 'b'), 52), ((53, Just 'c'), 57), ((53, Just 'd'), 57), ((53, Just 'e'), 57), ((53, Just 'f'), 57), ((53, Just 'g'), 57), ((53, Just 'h'), 57), ((53, Just 'i'), 57), ((53, Just 'j'), 57), ((53, Just 'k'), 57), ((53, Just 'l'), 57), ((53, Just 'm'), 57), ((53, Just 'n'), 57), ((53, Just 'o'), 57), ((53, Just 'p'), 57), ((53, Just 'q'), 57), ((53, Just 'r'), 57), ((53, Just 's'), 57), ((53, Just 't'), 57), ((53, Just 'u'), 57), ((53, Just 'v'), 57), ((53, Just 'w'), 57), ((53, Just 'x'), 57), ((53, Just 'y'), 57), ((53, Just 'z'), 57)
            , ((54, Just '0'), 57), ((54, Just '1'), 57), ((54, Just '2'), 57), ((54, Just '3'), 57), ((54, Just '4'), 57), ((54, Just '5'), 57), ((54, Just '6'), 57), ((54, Just '7'), 57), ((54, Just '8'), 57), ((54, Just '9'), 57), ((54, Just 'A'), 57), ((54, Just 'B'), 57), ((54, Just 'C'), 57), ((54, Just 'D'), 57), ((54, Just 'E'), 57), ((54, Just 'F'), 57), ((54, Just 'G'), 57), ((54, Just 'H'), 57), ((54, Just 'I'), 57), ((54, Just 'J'), 57), ((54, Just 'K'), 57), ((54, Just 'L'), 57), ((54, Just 'M'), 57), ((54, Just 'N'), 57), ((54, Just 'O'), 57), ((54, Just 'P'), 57), ((54, Just 'Q'), 57), ((54, Just 'R'), 57), ((54, Just 'S'), 57), ((54, Just 'T'), 57), ((54, Just 'U'), 57), ((54, Just 'V'), 57), ((54, Just 'W'), 57), ((54, Just 'X'), 57), ((54, Just 'Y'), 57), ((54, Just 'Z'), 57), ((54, Just '_'), 57), ((54, Just 'a'), 57), ((54, Just 'b'), 57), ((54, Just 'c'), 57), ((54, Just 'd'), 57), ((54, Just 'e'), 53), ((54, Just 'f'), 57), ((54, Just 'g'), 57), ((54, Just 'h'), 57), ((54, Just 'i'), 57), ((54, Just 'j'), 57), ((54, Just 'k'), 57), ((54, Just 'l'), 57), ((54, Just 'm'), 57), ((54, Just 'n'), 57), ((54, Just 'o'), 57), ((54, Just 'p'), 57), ((54, Just 'q'), 57), ((54, Just 'r'), 57), ((54, Just 's'), 57), ((54, Just 't'), 57), ((54, Just 'u'), 57), ((54, Just 'v'), 57), ((54, Just 'w'), 57), ((54, Just 'x'), 57), ((54, Just 'y'), 57), ((54, Just 'z'), 57)
            , ((55, Just '0'), 57), ((55, Just '1'), 57), ((55, Just '2'), 57), ((55, Just '3'), 57), ((55, Just '4'), 57), ((55, Just '5'), 57), ((55, Just '6'), 57), ((55, Just '7'), 57), ((55, Just '8'), 57), ((55, Just '9'), 57), ((55, Just 'A'), 57), ((55, Just 'B'), 57), ((55, Just 'C'), 57), ((55, Just 'D'), 57), ((55, Just 'E'), 57), ((55, Just 'F'), 57), ((55, Just 'G'), 57), ((55, Just 'H'), 57), ((55, Just 'I'), 57), ((55, Just 'J'), 57), ((55, Just 'K'), 57), ((55, Just 'L'), 57), ((55, Just 'M'), 57), ((55, Just 'N'), 57), ((55, Just 'O'), 57), ((55, Just 'P'), 57), ((55, Just 'Q'), 57), ((55, Just 'R'), 57), ((55, Just 'S'), 57), ((55, Just 'T'), 57), ((55, Just 'U'), 57), ((55, Just 'V'), 57), ((55, Just 'W'), 57), ((55, Just 'X'), 57), ((55, Just 'Y'), 57), ((55, Just 'Z'), 57), ((55, Just '_'), 57), ((55, Just 'a'), 57), ((55, Just 'b'), 57), ((55, Just 'c'), 57), ((55, Just 'd'), 57), ((55, Just 'e'), 57), ((55, Just 'f'), 57), ((55, Just 'g'), 57), ((55, Just 'h'), 57), ((55, Just 'i'), 63), ((55, Just 'j'), 57), ((55, Just 'k'), 57), ((55, Just 'l'), 57), ((55, Just 'm'), 57), ((55, Just 'n'), 57), ((55, Just 'o'), 57), ((55, Just 'p'), 57), ((55, Just 'q'), 57), ((55, Just 'r'), 57), ((55, Just 's'), 57), ((55, Just 't'), 57), ((55, Just 'u'), 57), ((55, Just 'v'), 57), ((55, Just 'w'), 57), ((55, Just 'x'), 57), ((55, Just 'y'), 57), ((55, Just 'z'), 57)
            , ((56, Just '0'), 57), ((56, Just '1'), 57), ((56, Just '2'), 57), ((56, Just '3'), 57), ((56, Just '4'), 57), ((56, Just '5'), 57), ((56, Just '6'), 57), ((56, Just '7'), 57), ((56, Just '8'), 57), ((56, Just '9'), 57), ((56, Just 'A'), 57), ((56, Just 'B'), 57), ((56, Just 'C'), 57), ((56, Just 'D'), 57), ((56, Just 'E'), 57), ((56, Just 'F'), 57), ((56, Just 'G'), 57), ((56, Just 'H'), 57), ((56, Just 'I'), 57), ((56, Just 'J'), 57), ((56, Just 'K'), 57), ((56, Just 'L'), 57), ((56, Just 'M'), 57), ((56, Just 'N'), 57), ((56, Just 'O'), 57), ((56, Just 'P'), 57), ((56, Just 'Q'), 57), ((56, Just 'R'), 57), ((56, Just 'S'), 57), ((56, Just 'T'), 57), ((56, Just 'U'), 57), ((56, Just 'V'), 57), ((56, Just 'W'), 57), ((56, Just 'X'), 57), ((56, Just 'Y'), 57), ((56, Just 'Z'), 57), ((56, Just '_'), 57), ((56, Just 'a'), 55), ((56, Just 'b'), 57), ((56, Just 'c'), 57), ((56, Just 'd'), 57), ((56, Just 'e'), 57), ((56, Just 'f'), 57), ((56, Just 'g'), 57), ((56, Just 'h'), 57), ((56, Just 'i'), 57), ((56, Just 'j'), 57), ((56, Just 'k'), 57), ((56, Just 'l'), 57), ((56, Just 'm'), 57), ((56, Just 'n'), 57), ((56, Just 'o'), 57), ((56, Just 'p'), 57), ((56, Just 'q'), 57), ((56, Just 'r'), 57), ((56, Just 's'), 57), ((56, Just 't'), 57), ((56, Just 'u'), 57), ((56, Just 'v'), 57), ((56, Just 'w'), 57), ((56, Just 'x'), 57), ((56, Just 'y'), 57), ((56, Just 'z'), 57)
            , ((57, Just '0'), 57), ((57, Just '1'), 57), ((57, Just '2'), 57), ((57, Just '3'), 57), ((57, Just '4'), 57), ((57, Just '5'), 57), ((57, Just '6'), 57), ((57, Just '7'), 57), ((57, Just '8'), 57), ((57, Just '9'), 57), ((57, Just 'A'), 57), ((57, Just 'B'), 57), ((57, Just 'C'), 57), ((57, Just 'D'), 57), ((57, Just 'E'), 57), ((57, Just 'F'), 57), ((57, Just 'G'), 57), ((57, Just 'H'), 57), ((57, Just 'I'), 57), ((57, Just 'J'), 57), ((57, Just 'K'), 57), ((57, Just 'L'), 57), ((57, Just 'M'), 57), ((57, Just 'N'), 57), ((57, Just 'O'), 57), ((57, Just 'P'), 57), ((57, Just 'Q'), 57), ((57, Just 'R'), 57), ((57, Just 'S'), 57), ((57, Just 'T'), 57), ((57, Just 'U'), 57), ((57, Just 'V'), 57), ((57, Just 'W'), 57), ((57, Just 'X'), 57), ((57, Just 'Y'), 57), ((57, Just 'Z'), 57), ((57, Just '_'), 57), ((57, Just 'a'), 57), ((57, Just 'b'), 57), ((57, Just 'c'), 57), ((57, Just 'd'), 57), ((57, Just 'e'), 57), ((57, Just 'f'), 57), ((57, Just 'g'), 57), ((57, Just 'h'), 57), ((57, Just 'i'), 57), ((57, Just 'j'), 57), ((57, Just 'k'), 57), ((57, Just 'l'), 57), ((57, Just 'm'), 57), ((57, Just 'n'), 57), ((57, Just 'o'), 57), ((57, Just 'p'), 57), ((57, Just 'q'), 57), ((57, Just 'r'), 57), ((57, Just 's'), 57), ((57, Just 't'), 57), ((57, Just 'u'), 57), ((57, Just 'v'), 57), ((57, Just 'w'), 57), ((57, Just 'x'), 57), ((57, Just 'y'), 57), ((57, Just 'z'), 57)
            , ((58, Just '0'), 57), ((58, Just '1'), 57), ((58, Just '2'), 57), ((58, Just '3'), 57), ((58, Just '4'), 57), ((58, Just '5'), 57), ((58, Just '6'), 57), ((58, Just '7'), 57), ((58, Just '8'), 57), ((58, Just '9'), 57), ((58, Just 'A'), 57), ((58, Just 'B'), 57), ((58, Just 'C'), 57), ((58, Just 'D'), 57), ((58, Just 'E'), 57), ((58, Just 'F'), 57), ((58, Just 'G'), 57), ((58, Just 'H'), 57), ((58, Just 'I'), 57), ((58, Just 'J'), 57), ((58, Just 'K'), 57), ((58, Just 'L'), 57), ((58, Just 'M'), 57), ((58, Just 'N'), 57), ((58, Just 'O'), 57), ((58, Just 'P'), 57), ((58, Just 'Q'), 57), ((58, Just 'R'), 57), ((58, Just 'S'), 57), ((58, Just 'T'), 57), ((58, Just 'U'), 57), ((58, Just 'V'), 57), ((58, Just 'W'), 57), ((58, Just 'X'), 57), ((58, Just 'Y'), 57), ((58, Just 'Z'), 57), ((58, Just '_'), 57), ((58, Just 'a'), 33), ((58, Just 'b'), 57), ((58, Just 'c'), 57), ((58, Just 'd'), 57), ((58, Just 'e'), 57), ((58, Just 'f'), 57), ((58, Just 'g'), 57), ((58, Just 'h'), 57), ((58, Just 'i'), 57), ((58, Just 'j'), 57), ((58, Just 'k'), 57), ((58, Just 'l'), 57), ((58, Just 'm'), 57), ((58, Just 'n'), 57), ((58, Just 'o'), 57), ((58, Just 'p'), 57), ((58, Just 'q'), 57), ((58, Just 'r'), 57), ((58, Just 's'), 57), ((58, Just 't'), 57), ((58, Just 'u'), 57), ((58, Just 'v'), 57), ((58, Just 'w'), 57), ((58, Just 'x'), 57), ((58, Just 'y'), 57), ((58, Just 'z'), 57)
            , ((59, Just '0'), 57), ((59, Just '1'), 57), ((59, Just '2'), 57), ((59, Just '3'), 57), ((59, Just '4'), 57), ((59, Just '5'), 57), ((59, Just '6'), 57), ((59, Just '7'), 57), ((59, Just '8'), 57), ((59, Just '9'), 57), ((59, Just 'A'), 57), ((59, Just 'B'), 57), ((59, Just 'C'), 57), ((59, Just 'D'), 57), ((59, Just 'E'), 57), ((59, Just 'F'), 57), ((59, Just 'G'), 57), ((59, Just 'H'), 57), ((59, Just 'I'), 57), ((59, Just 'J'), 57), ((59, Just 'K'), 57), ((59, Just 'L'), 57), ((59, Just 'M'), 57), ((59, Just 'N'), 57), ((59, Just 'O'), 57), ((59, Just 'P'), 57), ((59, Just 'Q'), 57), ((59, Just 'R'), 57), ((59, Just 'S'), 57), ((59, Just 'T'), 57), ((59, Just 'U'), 57), ((59, Just 'V'), 57), ((59, Just 'W'), 57), ((59, Just 'X'), 57), ((59, Just 'Y'), 57), ((59, Just 'Z'), 57), ((59, Just '_'), 57), ((59, Just 'a'), 57), ((59, Just 'b'), 57), ((59, Just 'c'), 57), ((59, Just 'd'), 42), ((59, Just 'e'), 57), ((59, Just 'f'), 57), ((59, Just 'g'), 57), ((59, Just 'h'), 57), ((59, Just 'i'), 57), ((59, Just 'j'), 57), ((59, Just 'k'), 57), ((59, Just 'l'), 57), ((59, Just 'm'), 57), ((59, Just 'n'), 57), ((59, Just 'o'), 57), ((59, Just 'p'), 57), ((59, Just 'q'), 57), ((59, Just 'r'), 57), ((59, Just 's'), 57), ((59, Just 't'), 57), ((59, Just 'u'), 57), ((59, Just 'v'), 57), ((59, Just 'w'), 57), ((59, Just 'x'), 57), ((59, Just 'y'), 57), ((59, Just 'z'), 57)
            , ((60, Just '0'), 57), ((60, Just '1'), 57), ((60, Just '2'), 57), ((60, Just '3'), 57), ((60, Just '4'), 57), ((60, Just '5'), 57), ((60, Just '6'), 57), ((60, Just '7'), 57), ((60, Just '8'), 57), ((60, Just '9'), 57), ((60, Just 'A'), 57), ((60, Just 'B'), 57), ((60, Just 'C'), 57), ((60, Just 'D'), 57), ((60, Just 'E'), 57), ((60, Just 'F'), 57), ((60, Just 'G'), 57), ((60, Just 'H'), 57), ((60, Just 'I'), 57), ((60, Just 'J'), 57), ((60, Just 'K'), 57), ((60, Just 'L'), 57), ((60, Just 'M'), 57), ((60, Just 'N'), 57), ((60, Just 'O'), 57), ((60, Just 'P'), 57), ((60, Just 'Q'), 57), ((60, Just 'R'), 57), ((60, Just 'S'), 57), ((60, Just 'T'), 57), ((60, Just 'U'), 57), ((60, Just 'V'), 57), ((60, Just 'W'), 57), ((60, Just 'X'), 57), ((60, Just 'Y'), 57), ((60, Just 'Z'), 57), ((60, Just '_'), 57), ((60, Just 'a'), 57), ((60, Just 'b'), 57), ((60, Just 'c'), 57), ((60, Just 'd'), 57), ((60, Just 'e'), 36), ((60, Just 'f'), 57), ((60, Just 'g'), 57), ((60, Just 'h'), 57), ((60, Just 'i'), 57), ((60, Just 'j'), 57), ((60, Just 'k'), 57), ((60, Just 'l'), 57), ((60, Just 'm'), 57), ((60, Just 'n'), 57), ((60, Just 'o'), 57), ((60, Just 'p'), 57), ((60, Just 'q'), 57), ((60, Just 'r'), 57), ((60, Just 's'), 57), ((60, Just 't'), 57), ((60, Just 'u'), 57), ((60, Just 'v'), 57), ((60, Just 'w'), 57), ((60, Just 'x'), 57), ((60, Just 'y'), 57), ((60, Just 'z'), 57)
            , ((61, Just '0'), 57), ((61, Just '1'), 57), ((61, Just '2'), 57), ((61, Just '3'), 57), ((61, Just '4'), 57), ((61, Just '5'), 57), ((61, Just '6'), 57), ((61, Just '7'), 57), ((61, Just '8'), 57), ((61, Just '9'), 57), ((61, Just 'A'), 57), ((61, Just 'B'), 57), ((61, Just 'C'), 57), ((61, Just 'D'), 57), ((61, Just 'E'), 57), ((61, Just 'F'), 57), ((61, Just 'G'), 57), ((61, Just 'H'), 57), ((61, Just 'I'), 57), ((61, Just 'J'), 57), ((61, Just 'K'), 57), ((61, Just 'L'), 57), ((61, Just 'M'), 57), ((61, Just 'N'), 57), ((61, Just 'O'), 57), ((61, Just 'P'), 57), ((61, Just 'Q'), 57), ((61, Just 'R'), 57), ((61, Just 'S'), 57), ((61, Just 'T'), 57), ((61, Just 'U'), 57), ((61, Just 'V'), 57), ((61, Just 'W'), 57), ((61, Just 'X'), 57), ((61, Just 'Y'), 57), ((61, Just 'Z'), 57), ((61, Just '_'), 57), ((61, Just 'a'), 57), ((61, Just 'b'), 57), ((61, Just 'c'), 57), ((61, Just 'd'), 57), ((61, Just 'e'), 43), ((61, Just 'f'), 57), ((61, Just 'g'), 57), ((61, Just 'h'), 57), ((61, Just 'i'), 57), ((61, Just 'j'), 57), ((61, Just 'k'), 57), ((61, Just 'l'), 57), ((61, Just 'm'), 57), ((61, Just 'n'), 57), ((61, Just 'o'), 57), ((61, Just 'p'), 57), ((61, Just 'q'), 57), ((61, Just 'r'), 57), ((61, Just 's'), 57), ((61, Just 't'), 57), ((61, Just 'u'), 57), ((61, Just 'v'), 57), ((61, Just 'w'), 57), ((61, Just 'x'), 57), ((61, Just 'y'), 57), ((61, Just 'z'), 57)
            , ((62, Just '0'), 57), ((62, Just '1'), 57), ((62, Just '2'), 57), ((62, Just '3'), 57), ((62, Just '4'), 57), ((62, Just '5'), 57), ((62, Just '6'), 57), ((62, Just '7'), 57), ((62, Just '8'), 57), ((62, Just '9'), 57), ((62, Just 'A'), 57), ((62, Just 'B'), 57), ((62, Just 'C'), 57), ((62, Just 'D'), 57), ((62, Just 'E'), 57), ((62, Just 'F'), 57), ((62, Just 'G'), 57), ((62, Just 'H'), 57), ((62, Just 'I'), 57), ((62, Just 'J'), 57), ((62, Just 'K'), 57), ((62, Just 'L'), 57), ((62, Just 'M'), 57), ((62, Just 'N'), 57), ((62, Just 'O'), 57), ((62, Just 'P'), 57), ((62, Just 'Q'), 57), ((62, Just 'R'), 57), ((62, Just 'S'), 57), ((62, Just 'T'), 57), ((62, Just 'U'), 57), ((62, Just 'V'), 57), ((62, Just 'W'), 57), ((62, Just 'X'), 57), ((62, Just 'Y'), 57), ((62, Just 'Z'), 57), ((62, Just '_'), 57), ((62, Just 'a'), 57), ((62, Just 'b'), 57), ((62, Just 'c'), 57), ((62, Just 'd'), 57), ((62, Just 'e'), 57), ((62, Just 'f'), 57), ((62, Just 'g'), 39), ((62, Just 'h'), 57), ((62, Just 'i'), 57), ((62, Just 'j'), 57), ((62, Just 'k'), 57), ((62, Just 'l'), 57), ((62, Just 'm'), 57), ((62, Just 'n'), 57), ((62, Just 'o'), 57), ((62, Just 'p'), 57), ((62, Just 'q'), 57), ((62, Just 'r'), 57), ((62, Just 's'), 57), ((62, Just 't'), 57), ((62, Just 'u'), 57), ((62, Just 'v'), 57), ((62, Just 'w'), 57), ((62, Just 'x'), 57), ((62, Just 'y'), 57), ((62, Just 'z'), 57)
            , ((63, Just '0'), 57), ((63, Just '1'), 57), ((63, Just '2'), 57), ((63, Just '3'), 57), ((63, Just '4'), 57), ((63, Just '5'), 57), ((63, Just '6'), 57), ((63, Just '7'), 57), ((63, Just '8'), 57), ((63, Just '9'), 57), ((63, Just 'A'), 57), ((63, Just 'B'), 57), ((63, Just 'C'), 57), ((63, Just 'D'), 57), ((63, Just 'E'), 57), ((63, Just 'F'), 57), ((63, Just 'G'), 57), ((63, Just 'H'), 57), ((63, Just 'I'), 57), ((63, Just 'J'), 57), ((63, Just 'K'), 57), ((63, Just 'L'), 57), ((63, Just 'M'), 57), ((63, Just 'N'), 57), ((63, Just 'O'), 57), ((63, Just 'P'), 57), ((63, Just 'Q'), 57), ((63, Just 'R'), 57), ((63, Just 'S'), 57), ((63, Just 'T'), 57), ((63, Just 'U'), 57), ((63, Just 'V'), 57), ((63, Just 'W'), 57), ((63, Just 'X'), 57), ((63, Just 'Y'), 57), ((63, Just 'Z'), 57), ((63, Just '_'), 57), ((63, Just 'a'), 57), ((63, Just 'b'), 57), ((63, Just 'c'), 57), ((63, Just 'd'), 57), ((63, Just 'e'), 57), ((63, Just 'f'), 57), ((63, Just 'g'), 57), ((63, Just 'h'), 57), ((63, Just 'i'), 57), ((63, Just 'j'), 57), ((63, Just 'k'), 57), ((63, Just 'l'), 37), ((63, Just 'm'), 57), ((63, Just 'n'), 57), ((63, Just 'o'), 57), ((63, Just 'p'), 57), ((63, Just 'q'), 57), ((63, Just 'r'), 57), ((63, Just 's'), 57), ((63, Just 't'), 57), ((63, Just 'u'), 57), ((63, Just 'v'), 57), ((63, Just 'w'), 57), ((63, Just 'x'), 57), ((63, Just 'y'), 57), ((63, Just 'z'), 57)
            , ((64, Just '0'), 57), ((64, Just '1'), 57), ((64, Just '2'), 57), ((64, Just '3'), 57), ((64, Just '4'), 57), ((64, Just '5'), 57), ((64, Just '6'), 57), ((64, Just '7'), 57), ((64, Just '8'), 57), ((64, Just '9'), 57), ((64, Just 'A'), 57), ((64, Just 'B'), 57), ((64, Just 'C'), 57), ((64, Just 'D'), 57), ((64, Just 'E'), 57), ((64, Just 'F'), 57), ((64, Just 'G'), 57), ((64, Just 'H'), 57), ((64, Just 'I'), 57), ((64, Just 'J'), 57), ((64, Just 'K'), 57), ((64, Just 'L'), 57), ((64, Just 'M'), 57), ((64, Just 'N'), 57), ((64, Just 'O'), 57), ((64, Just 'P'), 57), ((64, Just 'Q'), 57), ((64, Just 'R'), 57), ((64, Just 'S'), 57), ((64, Just 'T'), 57), ((64, Just 'U'), 57), ((64, Just 'V'), 57), ((64, Just 'W'), 57), ((64, Just 'X'), 57), ((64, Just 'Y'), 57), ((64, Just 'Z'), 57), ((64, Just '_'), 57), ((64, Just 'a'), 57), ((64, Just 'b'), 57), ((64, Just 'c'), 57), ((64, Just 'd'), 57), ((64, Just 'e'), 57), ((64, Just 'f'), 57), ((64, Just 'g'), 57), ((64, Just 'h'), 57), ((64, Just 'i'), 57), ((64, Just 'j'), 57), ((64, Just 'k'), 57), ((64, Just 'l'), 57), ((64, Just 'm'), 57), ((64, Just 'n'), 57), ((64, Just 'o'), 57), ((64, Just 'p'), 57), ((64, Just 'q'), 57), ((64, Just 'r'), 57), ((64, Just 's'), 38), ((64, Just 't'), 57), ((64, Just 'u'), 57), ((64, Just 'v'), 57), ((64, Just 'w'), 57), ((64, Just 'x'), 57), ((64, Just 'y'), 57), ((64, Just 'z'), 57)
            , ((65, Just '0'), 65), ((65, Just '1'), 65), ((65, Just '2'), 65), ((65, Just '3'), 65), ((65, Just '4'), 65), ((65, Just '5'), 65), ((65, Just '6'), 65), ((65, Just '7'), 65), ((65, Just '8'), 65), ((65, Just '9'), 65)
            , ((68, Just '\t'), 68), ((68, Just '\n'), 68), ((68, Just '\r'), 68), ((68, Just ' '), 68)
            , ((69, Just '\t'), 69), ((69, Just '\r'), 69), ((69, Just ' '), 69), ((69, Just '!'), 69), ((69, Just '"'), 69), ((69, Just '%'), 69), ((69, Just '\''), 69), ((69, Just '('), 69), ((69, Just ')'), 69), ((69, Just '*'), 69), ((69, Just '+'), 69), ((69, Just ','), 69), ((69, Just '-'), 69), ((69, Just '.'), 69), ((69, Just '/'), 69), ((69, Just '0'), 69), ((69, Just '1'), 69), ((69, Just '2'), 69), ((69, Just '3'), 69), ((69, Just '4'), 69), ((69, Just '5'), 69), ((69, Just '6'), 69), ((69, Just '7'), 69), ((69, Just '8'), 69), ((69, Just '9'), 69), ((69, Just ':'), 69), ((69, Just ';'), 69), ((69, Just '<'), 69), ((69, Just '='), 69), ((69, Just '>'), 69), ((69, Just '?'), 69), ((69, Just 'A'), 69), ((69, Just 'B'), 69), ((69, Just 'C'), 69), ((69, Just 'D'), 69), ((69, Just 'E'), 69), ((69, Just 'F'), 69), ((69, Just 'G'), 69), ((69, Just 'H'), 69), ((69, Just 'I'), 69), ((69, Just 'J'), 69), ((69, Just 'K'), 69), ((69, Just 'L'), 69), ((69, Just 'M'), 69), ((69, Just 'N'), 69), ((69, Just 'O'), 69), ((69, Just 'P'), 69), ((69, Just 'Q'), 69), ((69, Just 'R'), 69), ((69, Just 'S'), 69), ((69, Just 'T'), 69), ((69, Just 'U'), 69), ((69, Just 'V'), 69), ((69, Just 'W'), 69), ((69, Just 'X'), 69), ((69, Just 'Y'), 69), ((69, Just 'Z'), 69), ((69, Just '['), 69), ((69, Just '\\'), 69), ((69, Just ']'), 69), ((69, Just '_'), 69), ((69, Just 'a'), 69), ((69, Just 'b'), 69), ((69, Just 'c'), 69), ((69, Just 'd'), 69), ((69, Just 'e'), 69), ((69, Just 'f'), 69), ((69, Just 'g'), 69), ((69, Just 'h'), 69), ((69, Just 'i'), 69), ((69, Just 'j'), 69), ((69, Just 'k'), 69), ((69, Just 'l'), 69), ((69, Just 'm'), 69), ((69, Just 'n'), 69), ((69, Just 'o'), 69), ((69, Just 'p'), 69), ((69, Just 'q'), 69), ((69, Just 'r'), 69), ((69, Just 's'), 69), ((69, Just 't'), 69), ((69, Just 'u'), 69), ((69, Just 'v'), 69), ((69, Just 'w'), 69), ((69, Just 'x'), 69), ((69, Just 'y'), 69), ((69, Just 'z'), 69), ((69, Nothing), 69)
            ]
        }
    theAlphabet :: XSet.Set Char
    theAlphabet = XSet.fromAscList "\t\n\r !\"%'()*+,-./0123456789:;<=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]_abcdefghijklmnopqrstuvwxyz"
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
            ((35, this), ((row1, col1), (row2, col2))) -> return_one (T_id (SLoc (row1, col1) (row2, col2)) this)
            ((36, this), ((row1, col1), (row2, col2))) -> return_one (T_nat_lit (SLoc (row1, col1) (row2, col2)) (read this))
            ((37, this), ((row1, col1), (row2, col2))) -> return_one (mkStringToken (SLoc (row1, col1) (row2, col2)) this)
            ((38, this), ((row1, col1), (row2, col2))) -> return_one (mkCharToken (SLoc (row1, col1) (row2, col2)) this)
            ((39, this), ((row1, col1), (row2, col2))) -> return []
            ((40, this), ((row1, col1), (row2, col2))) -> return []
            ((41, this), ((row1, col1), (row2, col2))) -> return []
        tokens2 <- runHolLexerRaw_this str1
        return (tokens1 ++ tokens2)
