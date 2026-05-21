module Project.A.Go.Gen
    ( constantProgram
    , genProgram
    , genTestCase
    ) where

import Project.A.Go.AST
import Project.A.Types

constantProgram :: Program
constantProgram =
    Program
        [ SPrintln [EInt 3]
        ]

genTestCase :: CaseId -> Seed -> Size -> TestCase Program
genTestCase caseId seed size =
    TestCase
        { tcCaseId = caseId
        , tcSeed = seed
        , tcSize = size
        , tcProgram = genProgram seed size
        , tcInput =
            RuntimeInput
                { riArgs = []
                , riStdin = ""
                , riEnv = []
                }
        }

genProgram :: Seed -> Size -> Program
genProgram seed size
    | size <= 0 = constantProgram
    | otherwise =
        Program $
            [ SVar TInt "x" (EInt x0)
            , SVar TInt "y" (EInt y0)
            ]
                ++ guardedIf
                ++ guardedLoop
                ++ [ SPrintln [EAdd (EVar TInt "x") (EVar TInt "y")]
                   ]
  where
    n :: Int
    n = abs seed

    x0 :: Int
    x0 = n `mod` 17

    y0 :: Int
    y0 = (n `div` 7) `mod` 19

    guardedIf :: [Stmt]
    guardedIf =
        if size >= 2
            then
                [ SIf
                    (ELt (EVar TInt "x") (EVar TInt "y"))
                    [SAssign "x" (EAdd (EVar TInt "x") (EInt 1))]
                    [SAssign "y" (EAdd (EVar TInt "y") (EInt 1))]
                ]
            else []

    guardedLoop :: [Stmt]
    guardedLoop =
        if size >= 3
            then
                [ SForBounded
                    "i"
                    (1 + (n `mod` 4))
                    [ SAssign "x" (EAdd (EVar TInt "x") (EVar TInt "i"))
                    ]
                ]
            else []
