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

import Hol.BETA2.Header (SLoc (..))
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
diagnosticWithModule mode tag sourceName sourceLines loc body =
    render mode $ Doc.vcat
        (diagnosticHeader "error" tag sourceName loc : locBlockWith mode sourceLines loc : body)

diagnosticWarningWithModule :: DiagnosticMode -> String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWarningWithModule mode tag sourceName sourceLines loc body =
    render mode $ Doc.vcat
        (diagnosticHeader "warning" tag sourceName loc : locBlockWith mode sourceLines loc : body)

diagnosticAt :: String -> Int -> Int -> [Doc.Doc] -> String
diagnosticAt tag row col body =
    render DiagnosticPretty $ Doc.vcat
        (diagnosticHeader "error" tag Nothing (SLoc (row, col) (row, col)) : locBlockWith DiagnosticPretty Nothing (SLoc (row, col) (row, col)) : body)

diagnosticNoLoc :: String -> [Doc.Doc] -> String
diagnosticNoLoc = diagnosticNoLocWith DiagnosticPretty

diagnosticNoLocWith :: DiagnosticMode -> String -> [Doc.Doc] -> String
diagnosticNoLocWith mode tag body =
    render mode $ Doc.vcat (severityDoc "error" <> Doc.text (" [" ++ tag ++ "]") : body)

locBlock :: SourceLines -> SLoc -> Doc.Doc
locBlock = locBlockWith DiagnosticPretty

locBlockWith :: DiagnosticMode -> SourceLines -> SLoc -> Doc.Doc
locBlockWith mode sourceLines (SLoc (row, col) (endRow, endCol)) =
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
    colorSource = case mode of
        DiagnosticPretty -> Doc.red
        DiagnosticTest -> id
    focusWidth = max 1 (if row == endRow then endCol - col + 1 else 1)
    sourceDoc = Doc.text " " <> maybe mempty highlightedLine (sourceLines >>= lineAt row)
    caretDoc = Doc.text " " <> Doc.text (replicate (max 0 (col - 1)) ' ') <> colorCaret (Doc.textbf (replicate focusWidth '^'))
    highlightedLine line =
        let beforeLen = max 0 (col - 1)
            (before, rest) = splitAt beforeLen line
            (focus, after) = splitAt focusWidth rest
        in Doc.text before <> colorSource (Doc.textbf focus) <> Doc.text after
    lineAt :: Int -> [String] -> Maybe String
    lineAt n xs
        | n <= 0 = Nothing
        | otherwise = case drop (n - 1) xs of
            line : _ -> Just line
            [] -> Nothing

ghcLoc :: SLoc -> String
ghcLoc (SLoc (row, col) (endRow, endCol)) = show row ++ ":" ++ show col ++ "-" ++ show endRow ++ ":" ++ show endCol

locPrefix :: Maybe String -> SLoc -> String
locPrefix Nothing loc = ghcLoc loc
locPrefix (Just sourceName) loc = sourceName ++ ":" ++ ghcLoc loc

diagnosticHeader :: String -> String -> Maybe String -> SLoc -> Doc.Doc
diagnosticHeader severity tag sourceName loc =
    Doc.textbf (locPrefix sourceName loc) <> Doc.text ": " <> severityDoc severity <> Doc.text (" [" ++ tag ++ "]")

severityDoc :: String -> Doc.Doc
severityDoc "error" = Doc.red (Doc.textbf "error:")
severityDoc severity = Doc.textbf (severity ++ ":")

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
