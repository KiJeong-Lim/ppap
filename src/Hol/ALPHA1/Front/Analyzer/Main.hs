module Hol.ALPHA1.Front.Analyzer.Main where

import Hol.ALPHA1.Front.Analyzer.Grammar
import Hol.ALPHA1.Front.Analyzer.Lexer
import Hol.ALPHA1.Front.Analyzer.Parser
import Hol.ALPHA1.Front.Header

type AnalyzerOuput = Either TermRep [DeclRep]

runAnalyzer :: String -> Either ErrMsg AnalyzerOuput
runAnalyzer src0
    = case runAladdinLexer src0 of
        Left (row, col) -> Left ("*** lexing error at { row = " ++ showsPrec 0 row (", col = " ++ showsPrec 0 col " }."))
        Right src1 -> case runAladdinParser src1 of
            Left Nothing -> Left ("*** parsing error at EOF.")
            Left (Just token) -> case getSLoc token of
                SLoc (row1, col1) (row2, col2) -> Left ("*** parsing error at { row = " ++ showsPrec 0 row1 (", col = " ++ showsPrec 0 col1 " }."))
            Right output -> Right output
