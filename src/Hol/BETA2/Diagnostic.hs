module Hol.BETA2.Diagnostic
    ( DiagnosticMode (..)
    , SourceLines
    , diagnostic
    , diagnosticWith
    , diagnosticInModule
    , diagnosticWithModule
    , diagnosticWarningWithModule
    , diagnosticAt
    , diagnosticNoLoc
    , diagnosticNoLocWith
    , locBlock
    , locBlockWith
    ) where

import Hol.BETA2.Header (SLoc (..), pprintMSLoc)
import qualified Z.Doc as Doc

type SourceLines = Maybe [String]

data DiagnosticMode
    = DiagnosticPretty
    | DiagnosticTest
    deriving (Eq, Ord, Show)

diagnostic :: String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnostic = diagnosticWith DiagnosticPretty

diagnosticWith :: DiagnosticMode -> String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWith mode tag sourceLines loc body =
    diagnosticWithModule mode tag Nothing sourceLines loc body

diagnosticInModule :: String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticInModule = diagnosticWithModule DiagnosticPretty

diagnosticWithModule :: DiagnosticMode -> String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWithModule mode tag moduleName sourceLines loc body =
    render mode $ Doc.vcat
        (Doc.text (locPrefix moduleName loc ++ ": error: [" ++ tag ++ "]") : locBlockWith mode sourceLines loc : body)

diagnosticWarningWithModule :: DiagnosticMode -> String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWarningWithModule mode tag moduleName sourceLines loc body =
    render mode $ Doc.vcat
        (Doc.text (locPrefix moduleName loc ++ ": warning: [" ++ tag ++ "]") : locBlockWith mode sourceLines loc : body)

diagnosticAt :: String -> Int -> Int -> [Doc.Doc] -> String
diagnosticAt tag row col body =
    render DiagnosticPretty $ Doc.vcat
        (Doc.text (show row ++ ":" ++ show col ++ ": error: [" ++ tag ++ "]") : locBlockWith DiagnosticPretty Nothing (SLoc (row, col) (row, col)) : body)

diagnosticNoLoc :: String -> [Doc.Doc] -> String
diagnosticNoLoc = diagnosticNoLocWith DiagnosticPretty

diagnosticNoLocWith :: DiagnosticMode -> String -> [Doc.Doc] -> String
diagnosticNoLocWith mode tag body =
    render mode $ Doc.vcat (Doc.text ("error: [" ++ tag ++ "]") : body)

locBlock :: SourceLines -> SLoc -> Doc.Doc
locBlock = locBlockWith DiagnosticPretty

locBlockWith :: DiagnosticMode -> SourceLines -> SLoc -> Doc.Doc
locBlockWith mode sourceLines (SLoc (row, col) _) =
    mconcat
        [ Doc.vcat [Doc.text "", colorLineNo (mconcat [Doc.text " ", Doc.ptext row, Doc.text " "]), Doc.text ""]
        , colorLineNo (Doc.beam '|')
        , Doc.vcat [Doc.text "", sourceDoc, caretDoc]
        ]
  where
    colorLineNo = case mode of
        DiagnosticPretty -> Doc.blue
        DiagnosticTest -> id
    colorCaret = case mode of
        DiagnosticPretty -> Doc.red
        DiagnosticTest -> id
    sourceDoc = Doc.text " " <> maybe mempty Doc.text (sourceLines >>= lineAt row)
    caretDoc = Doc.text " " <> Doc.text (replicate (max 0 (col - 1)) ' ') <> colorCaret (Doc.beam '^')
    lineAt :: Int -> [String] -> Maybe String
    lineAt n xs
        | n <= 0 = Nothing
        | otherwise = case drop (n - 1) xs of
            line : _ -> Just line
            [] -> Nothing

ghcLoc :: SLoc -> String
ghcLoc (SLoc (row, col) _) = show row ++ ":" ++ show col

locPrefix :: Maybe String -> SLoc -> String
locPrefix Nothing loc = ghcLoc loc
locPrefix moduleName loc = pprintMSLoc moduleName loc ""

render :: DiagnosticMode -> Doc.Doc -> String
render DiagnosticPretty = Doc.renderDoc
render DiagnosticTest = stripAnsi . Doc.renderDoc

stripAnsi :: String -> String
stripAnsi [] = []
stripAnsi ('\ESC' : '[' : rest) = stripAnsi (dropAnsi rest)
stripAnsi (ch : rest) = ch : stripAnsi rest

dropAnsi :: String -> String
dropAnsi [] = []
dropAnsi (ch : rest)
    | ch >= '@' && ch <= '~' = rest
    | otherwise = dropAnsi rest
