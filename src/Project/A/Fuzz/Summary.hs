module Project.A.Fuzz.Summary
    ( Summary (..)
    , emptySummary
    , addReport
    , renderSummary
    ) where

import Project.A.Go.AST
import Project.A.Types

data Summary = Summary
    { summaryCases :: Int
    , summaryPass :: Int
    , summaryDiscard :: Int
    , summaryFail :: Int
    , summaryInconclusive :: Int
    } deriving (Eq, Ord, Show)

emptySummary :: Summary
emptySummary =
    Summary
        { summaryCases = 0
        , summaryPass = 0
        , summaryDiscard = 0
        , summaryFail = 0
        , summaryInconclusive = 0
        }

addReport :: Summary -> CaseReport Program -> Summary
addReport summary report =
    case crStatus report of
        CasePass ->
            bump (\s -> s { summaryPass = summaryPass s + 1 })
        CaseDiscard ->
            bump (\s -> s { summaryDiscard = summaryDiscard s + 1 })
        CaseFail _ ->
            bump (\s -> s { summaryFail = summaryFail s + 1 })
        CaseInconclusive ->
            bump (\s -> s { summaryInconclusive = summaryInconclusive s + 1 })
  where
    bump f = f (summary { summaryCases = summaryCases summary + 1 })

renderSummary :: Summary -> String
renderSummary summary =
    unlines
        [ "cases: " ++ show (summaryCases summary)
        , "pass: " ++ show (summaryPass summary)
        , "discard: " ++ show (summaryDiscard summary)
        , "fail: " ++ show (summaryFail summary)
        , "inconclusive: " ++ show (summaryInconclusive summary)
        ]
