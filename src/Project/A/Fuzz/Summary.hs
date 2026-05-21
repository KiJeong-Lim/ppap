module Project.A.Fuzz.Summary where

import Project.A.Go.AST
import Project.A.Types
import Z.Utils

data Summary
    = Summary
    { summaryCases :: Int
    , summaryPass :: Int
    , summaryDiscard :: Int
    , summaryFail :: Int
    , summaryInconclusive :: Int
    } deriving (Eq, Ord, Show)

emptySummary :: Summary
emptySummary = Summary { summaryCases = 0, summaryPass = 0, summaryDiscard = 0, summaryFail = 0, summaryInconclusive = 0 }

addReport :: Summary -> CaseReport Program -> Summary
addReport summary report
    = case crStatus report of
        CasePass -> bump (\s -> s { summaryPass = summaryPass s + 1 })
        CaseDiscard -> bump (\s -> s { summaryDiscard = summaryDiscard s + 1 })
        CaseFail _ -> bump (\s -> s { summaryFail = summaryFail s + 1 })
        CaseInconclusive -> bump (\s -> s { summaryInconclusive = summaryInconclusive s + 1 })
    where
        bump f = f (summary { summaryCases = summaryCases summary + 1 })

renderSummary :: Summary -> String
renderSummary = withZero . showSummary

showSummary :: Summary -> ShowS
showSummary summary = strcat
    [ strstr "cases: " . shows (summaryCases summary) . nl
    , strstr "pass: " . shows (summaryPass summary) . nl
    , strstr "discard: " . shows (summaryDiscard summary) . nl
    , strstr "fail: " . shows (summaryFail summary) . nl
    , strstr "inconclusive: " . shows (summaryInconclusive summary) . nl
    ]
