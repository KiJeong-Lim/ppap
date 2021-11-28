module Jasmine.Alpha1.Analyzer.Grammar where

import Jasmine.Alpha1.Header.Export

data Token
    = T_SmallId SrcLoc SmallId
    | T_LargeId SrcLoc LargeId
    | T_Symbol1 SrcLoc SmallId
    | T_Symbol2 SrcLoc LargeId
    | T_nat_lit SrcLoc Integer
    | T_chr_lit SrcLoc Char
    | T_str_lit SrcLoc String
    | T_lparen SrcLoc -- (
    | T_rparen SrcLoc -- )
    | T_lbracket SrcLoc -- [
    | T_rbracket SrcLoc -- ]
    | T_lbrace SrcLoc -- {
    | T_rbrace SrcLoc -- }
    | T_bslash SrcLoc -- \
    | T_comma SrcLoc -- ,
    | T_semicolon SrcLoc -- ;
    | T_colon SrcLoc -- :
    | T_equal SrcLoc -- =
    | T_bang SrcLoc -- !
    | T_import SrcLoc ModName
    | T_module SrcLoc ModName
    | T_preprocess SrcLoc JasminePP
    | T_pragma SrcLoc JasminePragma
    deriving (Eq, Ord, Show)

instance HasSrcLoc (Token) where
    getSrcLoc tok = case tok of
        T_SmallId loc _ -> loc
        T_LargeId loc _ -> loc
        T_Symbol1 loc _ -> loc
        T_Symbol2 loc _ -> loc
        T_nat_lit loc _ -> loc
        T_chr_lit loc _ -> loc
        T_str_lit loc _ -> loc
        T_lparen loc -> loc
        T_rparen loc -> loc
        T_lbracket loc -> loc
        T_rbracket loc -> loc
        T_lbrace loc -> loc
        T_rbrace loc -> loc
        T_bslash loc -> loc
        T_comma loc -> loc
        T_semicolon loc -> loc
        T_colon loc -> loc
        T_equal loc -> loc
        T_bang loc -> loc
        T_import loc _ -> loc
        T_module loc _ -> loc
        T_preprocess loc _ -> loc
        T_pragma loc _ -> loc
