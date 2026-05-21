module Project.A.Fuzz.Score where

import qualified Data.List as List

import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Go.Shrink
import Project.A.Types
import qualified Project.A.Util.Json as Json

data Score
    = FoundCounterexample Failure
    | Interesting Int [RiskSignal]
    | Irrelevant
    deriving (Eq, Ord, Show)

data RiskSignal
    = RiskDivision
    | RiskModulo
    | RiskNegativeDivOperand
    | RiskNegativeDivisor
    | RiskShortCircuit
    | RiskLoopBoundary
    | RiskConstantCondition
    | RiskOverflowBoundary
    | RiskShadowing
    | RiskZeroLiteral
    | RiskNegativeLiteral
    | RiskTimeout
    deriving (Eq, Ord, Show)

scoreOfReport :: CaseReport Program -> Score
scoreOfReport report
    = case crStatus report of
        CaseFail failure -> FoundCounterexample failure
        CaseDiscard -> Irrelevant
        CaseInconclusive -> Interesting 1 [RiskTimeout]
        CasePass -> scoreOfProgram (tcProgram (crTestCase report))

scoreOfProgram :: Program -> Score
scoreOfProgram program = Interesting (programScoreDistance program) (riskSignalsOf program)

programScoreDistance :: Program -> Int
programScoreDistance program = max 1 (100 + programNodeCount program - riskWeight (riskSignalsOf program))

scoreValue :: Score -> Maybe Int
scoreValue (FoundCounterexample _) = Just 0
scoreValue (Interesting n _) = Just n
scoreValue Irrelevant = Nothing

scoreJson :: Score -> String
scoreJson (FoundCounterexample failure) = Json.object
    [ Json.field "tag" (Json.string "FoundCounterexample")
    , Json.field "value" (Json.int 0)
    , Json.field "failure" (Json.string (show failure))
    , Json.field "risks" (Json.list Json.string [])
    ]
scoreJson (Interesting n risks) = Json.object
    [ Json.field "tag" (Json.string "Interesting")
    , Json.field "value" (Json.int n)
    , Json.field "risks" (Json.list (Json.string . show) risks)
    ]
scoreJson Irrelevant = Json.object
    [ Json.field "tag" (Json.string "Irrelevant")
    , Json.field "value" "null"
    , Json.field "risks" (Json.list Json.string [])
    ]

scoreSummary :: Score -> String
scoreSummary (FoundCounterexample failure) = "counterexample: " ++ show failure
scoreSummary (Interesting n risks) = "score=" ++ show n ++ ", risks=" ++ show risks
scoreSummary Irrelevant = "irrelevant"

riskSignalsOf :: Program -> [RiskSignal]
riskSignalsOf program = List.nub (featureRisks (featuresOf program) ++ programRiskSignals program)

featureRisks :: [Feature] -> [RiskSignal]
featureRisks features = concat
    [ if UsesDivision `elem` features then [RiskDivision] else []
    , if UsesModulo `elem` features then [RiskModulo] else []
    , if UsesShortCircuit `elem` features then [RiskShortCircuit] else []
    , if UsesShadowing `elem` features then [RiskShadowing] else []
    , if UsesZeroLiteral `elem` features then [RiskZeroLiteral] else []
    , if UsesNegativeLiteral `elem` features then [RiskNegativeLiteral] else []
    ]

programRiskSignals :: Program -> [RiskSignal]
programRiskSignals (Program funcs stmts) = concatMap funcRiskSignals funcs ++ concatMap stmtRiskSignals stmts

funcRiskSignals :: Func -> [RiskSignal]
funcRiskSignals func = concatMap stmtRiskSignals (funcBody func)

stmtRiskSignals :: Stmt -> [RiskSignal]
stmtRiskSignals stmt
    = case stmt of
        SVar _ _ expr -> exprRiskSignals expr
        SVarZero ty _ -> tyRiskSignals ty
        STypeDecl _ ty -> tyRiskSignals ty
        SShortVar ty _ expr -> tyRiskSignals ty ++ exprRiskSignals expr
        SShortVarCall vars _ args -> concatMap (tyRiskSignals . fst) vars ++ concatMap exprRiskSignals args
        SAssign _ expr -> exprRiskSignals expr
        SAssignCall _ _ args -> concatMap exprRiskSignals args
        SOpAssign _ _ expr -> exprRiskSignals expr
        SIndexAssign target index expr -> exprRiskSignals target ++ exprRiskSignals index ++ exprRiskSignals expr
        SDerefAssign target expr -> exprRiskSignals target ++ exprRiskSignals expr
        SBlock stmts -> concatMap stmtRiskSignals stmts
        SIf cond thn els -> conditionRisk cond ++ exprRiskSignals cond ++ concatMap stmtRiskSignals thn ++ concatMap stmtRiskSignals els
        SForBounded _ bound body -> loopRisk bound ++ concatMap stmtRiskSignals body
        SPrintln exprs -> concatMap exprRiskSignals exprs
        SExpr expr -> exprRiskSignals expr
        SBlank expr -> exprRiskSignals expr
        SReturn exprs -> concatMap exprRiskSignals exprs

exprRiskSignals :: Expr -> [RiskSignal]
exprRiskSignals expr
    = case expr of
        EInt n -> intRisk n
        EBool _ -> []
        EString _ -> []
        ENil ty -> tyRiskSignals ty
        EVar _ _ -> []
        EAdd lhs rhs -> binaryRisk lhs rhs
        ESub lhs rhs -> binaryRisk lhs rhs
        EMul lhs rhs -> binaryRisk lhs rhs
        EDiv lhs rhs -> RiskDivision : divRisk lhs rhs ++ binaryRisk lhs rhs
        EMod lhs rhs -> RiskModulo : divRisk lhs rhs ++ binaryRisk lhs rhs
        EEq lhs rhs -> binaryRisk lhs rhs
        ENe lhs rhs -> binaryRisk lhs rhs
        ELt lhs rhs -> binaryRisk lhs rhs
        ELe lhs rhs -> binaryRisk lhs rhs
        EGt lhs rhs -> binaryRisk lhs rhs
        EGe lhs rhs -> binaryRisk lhs rhs
        ENot arg -> exprRiskSignals arg
        EAnd lhs rhs -> RiskShortCircuit : binaryRisk lhs rhs
        EOr lhs rhs -> RiskShortCircuit : binaryRisk lhs rhs
        EArrayLit ty exprs -> tyRiskSignals ty ++ concatMap exprRiskSignals exprs
        ESliceLit ty exprs -> tyRiskSignals ty ++ concatMap exprRiskSignals exprs
        EStructLit ty fields -> tyRiskSignals ty ++ concatMap (exprRiskSignals . snd) fields
        EIndex ty target index -> tyRiskSignals ty ++ exprRiskSignals target ++ exprRiskSignals index
        EField ty target _ -> tyRiskSignals ty ++ exprRiskSignals target
        ELen expr -> exprRiskSignals expr
        ECall ty _ args -> tyRiskSignals ty ++ concatMap exprRiskSignals args
        EAddr expr -> exprRiskSignals expr
        EDeref ty expr -> tyRiskSignals ty ++ exprRiskSignals expr

binaryRisk :: Expr -> Expr -> [RiskSignal]
binaryRisk lhs rhs = exprRiskSignals lhs ++ exprRiskSignals rhs

divRisk :: Expr -> Expr -> [RiskSignal]
divRisk lhs rhs = concat
    [ if containsNegativeInt lhs || containsNegativeInt rhs then [RiskNegativeDivOperand] else []
    , if containsNegativeInt rhs then [RiskNegativeDivisor] else []
    ]

conditionRisk :: Expr -> [RiskSignal]
conditionRisk (EBool _) = [RiskConstantCondition]
conditionRisk _ = []

loopRisk :: Int -> [RiskSignal]
loopRisk bound
    | bound <= 1 = [RiskLoopBoundary]
    | otherwise = []

intRisk :: Int -> [RiskSignal]
intRisk n = concat
    [ if n == 0 then [RiskZeroLiteral] else []
    , if n < 0 then [RiskNegativeLiteral] else []
    , if abs n >= overflowBoundary then [RiskOverflowBoundary] else []
    ]

containsNegativeInt :: Expr -> Bool
containsNegativeInt expr
    = case expr of
        EInt n -> n < 0
        EBool _ -> False
        EString _ -> False
        ENil _ -> False
        EVar _ _ -> False
        EAdd lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        ESub lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EMul lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EDiv lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EMod lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EEq lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        ENe lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        ELt lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        ELe lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EGt lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EGe lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        ENot arg -> containsNegativeInt arg
        EAnd lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EOr lhs rhs -> containsNegativeInt lhs || containsNegativeInt rhs
        EArrayLit _ exprs -> any containsNegativeInt exprs
        ESliceLit _ exprs -> any containsNegativeInt exprs
        EStructLit _ fields -> any (containsNegativeInt . snd) fields
        EIndex _ target index -> containsNegativeInt target || containsNegativeInt index
        EField _ target _ -> containsNegativeInt target
        ELen arg -> containsNegativeInt arg
        ECall _ _ args -> any containsNegativeInt args
        EAddr arg -> containsNegativeInt arg
        EDeref _ arg -> containsNegativeInt arg

tyRiskSignals :: Ty -> [RiskSignal]
tyRiskSignals TInt = []
tyRiskSignals TBool = []
tyRiskSignals TString = []
tyRiskSignals (TArray _ ty) = tyRiskSignals ty
tyRiskSignals (TSlice ty) = tyRiskSignals ty
tyRiskSignals (TPointer ty) = tyRiskSignals ty
tyRiskSignals (TNamed _) = []
tyRiskSignals (TStruct fields) = concatMap (tyRiskSignals . fst) fields

riskWeight :: [RiskSignal] -> Int
riskWeight = sum . map riskSignalWeight

riskSignalWeight :: RiskSignal -> Int
riskSignalWeight RiskDivision = 20
riskSignalWeight RiskModulo = 20
riskSignalWeight RiskNegativeDivOperand = 15
riskSignalWeight RiskNegativeDivisor = 20
riskSignalWeight RiskShortCircuit = 10
riskSignalWeight RiskLoopBoundary = 15
riskSignalWeight RiskConstantCondition = 5
riskSignalWeight RiskOverflowBoundary = 30
riskSignalWeight RiskShadowing = 15
riskSignalWeight RiskZeroLiteral = 5
riskSignalWeight RiskNegativeLiteral = 5
riskSignalWeight RiskTimeout = 50

overflowBoundary :: Int
overflowBoundary = 1000000000
