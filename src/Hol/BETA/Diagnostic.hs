module Hol.BETA.Diagnostic
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
    , eofSLoc
    , locBlock
    , locBlockWith
    ) where

import Hol.BETA.Header (SLoc (..))
import qualified Z.Doc as Doc

type SourceLines = Maybe [String]

data DiagnosticMode
    = DiagnosticPretty
    | DiagnosticTest
    deriving (Eq, Ord, Show)

diagnostic :: String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnostic = diagnosticWith DiagnosticPretty

diagnosticWith :: DiagnosticMode -> String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWith mode tag sourceLines loc body = diagnosticWithModule mode tag Nothing sourceLines loc body

diagnosticInModule :: String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticInModule = diagnosticWithModule DiagnosticPretty

diagnosticWithModule :: DiagnosticMode -> String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWithModule mode tag sourceName sourceLines loc body = render mode $ Doc.vcat (diagnosticHeader "error" tag sourceName loc : locBlockWith mode sourceLines loc : body)

diagnosticWarningWithModule :: DiagnosticMode -> String -> Maybe String -> SourceLines -> SLoc -> [Doc.Doc] -> String
diagnosticWarningWithModule mode tag sourceName sourceLines loc body = render mode $ Doc.vcat (diagnosticHeader "warning" tag sourceName loc : locBlockWith mode sourceLines loc : body)

diagnosticAt :: String -> Int -> Int -> [Doc.Doc] -> String
diagnosticAt tag row col body = render DiagnosticPretty $ Doc.vcat (diagnosticHeader "error" tag Nothing (SLoc (row, col) (row, col)) : locBlockWith DiagnosticPretty Nothing (SLoc (row, col) (row, col)) : body)

diagnosticNoLoc :: String -> [Doc.Doc] -> String
diagnosticNoLoc = diagnosticNoLocWith DiagnosticPretty

diagnosticNoLocWith :: DiagnosticMode -> String -> [Doc.Doc] -> String
diagnosticNoLocWith mode tag body = render mode $ Doc.vcat (severityDoc "error" <> Doc.text (" [" ++ tag ++ "]") : body)

eofSLoc :: String -> SLoc
eofSLoc src = SLoc pos pos where
    pos = foldl advance (1, 1) src
    advance (row, _) '\n' = (row + 1, 1)
    advance (row, col) _ = (row, col + 1)

locBlock :: SourceLines -> SLoc -> Doc.Doc
locBlock = locBlockWith DiagnosticPretty

locBlockWith :: DiagnosticMode -> SourceLines -> SLoc -> Doc.Doc
locBlockWith mode sourceLines (SLoc (row, col) (endRow, endCol))
    | endRow <= row = singleLineBlock
    | otherwise = multilineBlock
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
        singleLineBlock = mconcat
            [ Doc.vcat [Doc.text "", colorLineNo (mconcat [Doc.text " ", Doc.ptext row, Doc.text " "]), Doc.text ""]
            , colorLineNo (Doc.beam '|')
            , Doc.vcat [Doc.text "", sourceDoc, caretDoc]
            ]
        sourceLine = sourceLines >>= lineAt row
        focusWidth = max 1 (if row == endRow then endCol - col + 1 else 1)
        sourceDoc = Doc.text " " <> maybe mempty highlightedLine sourceLine
        caretDoc = Doc.text " " <> Doc.text (maybe (replicate (max 0 (col - 1)) ' ') (caretIndent col) sourceLine) <> colorCaret (Doc.textbf (replicate focusWidth '^'))
        highlightedLine line = Doc.text before <> colorSource (Doc.textbf focus) <> Doc.text after where
            beforeLen = max 0 (col - 1)
            (before, rest) = splitAt beforeLen line
            (focus, after) = splitAt focusWidth rest
        multilineBlock = Doc.vcat (concatMap renderSourceRow [row .. endRow])
        gutterWidth = length (show endRow)
        renderSourceRow currentRow = case sourceLines >>= lineAt currentRow of
            Nothing -> [linePrefix currentRow, caretPrefix <> missingCaretRow currentRow]
            Just line -> [linePrefix currentRow <> highlightedRow currentRow line, caretPrefix <> caretRow currentRow line]
        linePrefix currentRow = colorLineNo (Doc.text (replicate (gutterWidth - length (show currentRow)) ' ' ++ show currentRow ++ " | "))
        caretPrefix = colorLineNo (Doc.text (replicate gutterWidth ' ' ++ " | "))
        highlightedRow currentRow line = Doc.text before <> colorSource (Doc.textbf focus) <> Doc.text after where
            (before, rest) = splitAt (rowStart currentRow - 1) line
            (focus, after) = splitAt (rowWidth currentRow line) rest
        caretRow currentRow line = Doc.text (caretIndent (rowStart currentRow) line) <> colorCaret (Doc.textbf (replicate (rowWidth currentRow line) '^'))
        missingCaretRow currentRow = Doc.text (replicate (rowStart currentRow - 1) ' ')
            <> colorCaret (Doc.textbf (replicate (if currentRow == endRow then max 1 endCol else 1) '^'))
        rowStart currentRow = if currentRow == row then max 1 col else 1
        rowWidth currentRow line = max 1 (rowEnd currentRow line - rowStart currentRow + 1)
        rowEnd currentRow line
            | currentRow == endRow = max (rowStart currentRow) endCol
            | otherwise = max (rowStart currentRow) (length line)
        lineAt :: Int -> [String] -> Maybe String
        lineAt n xs
            | n <= 0 = Nothing
            | otherwise = case drop (n - 1) xs of
                line : _ -> Just line
                [] -> Nothing
        caretIndent start line = map blankForCaret prefix ++ replicate missing ' ' where
            wanted = max 0 (start - 1)
            prefix = take wanted line
            missing = wanted - length prefix
            blankForCaret '\t' = '\t'
            blankForCaret _ = ' '

ghcLoc :: SLoc -> String
ghcLoc (SLoc (row, col) (endRow, endCol)) = show row ++ ":" ++ show col ++ "-" ++ show endRow ++ ":" ++ show endCol

locPrefix :: Maybe String -> SLoc -> String
locPrefix Nothing loc = ghcLoc loc
locPrefix (Just sourceName) loc = sourceName ++ ":" ++ ghcLoc loc

diagnosticHeader :: String -> String -> Maybe String -> SLoc -> Doc.Doc
diagnosticHeader severity tag sourceName loc = Doc.textbf (locPrefix sourceName loc) <> Doc.text ": " <> severityDoc severity <> Doc.text (" [" ++ tag ++ "]")

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
dropAnsi []
    = []
dropAnsi (ch : rest)
    | ch >= '@' && ch <= '~' = rest
    | otherwise = dropAnsi rest
