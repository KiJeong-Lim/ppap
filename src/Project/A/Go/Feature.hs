module Project.A.Go.Feature where

import qualified Data.List as List

import Project.A.Go.AST

data Feature
    = UsesIf
    | UsesFor
    | UsesDivision
    | UsesModulo
    | UsesShortCircuit
    | UsesNestedBlock
    | UsesShadowing
    | UsesString
    | UsesMultiplePrint
    | UsesZeroLiteral
    | UsesNegativeLiteral
    | UsesZeroInit
    | UsesShortVar
    | UsesCompoundAssign
    | UsesArray
    | UsesSlice
    | UsesIndex
    | UsesFunctionDecl
    | UsesFunctionCall
    | UsesMultipleReturn
    | UsesTypeDecl
    | UsesStruct
    | UsesPointer
    | UsesField
    deriving (Eq, Ord, Show)

allFeatures :: [Feature]
allFeatures =
    [ UsesIf
    , UsesFor
    , UsesDivision
    , UsesModulo
    , UsesShortCircuit
    , UsesNestedBlock
    , UsesShadowing
    , UsesString
    , UsesMultiplePrint
    , UsesZeroLiteral
    , UsesNegativeLiteral
    , UsesZeroInit
    , UsesShortVar
    , UsesCompoundAssign
    , UsesArray
    , UsesSlice
    , UsesIndex
    , UsesFunctionDecl
    , UsesFunctionCall
    , UsesMultipleReturn
    , UsesTypeDecl
    , UsesStruct
    , UsesPointer
    , UsesField
    ]

featuresOf :: Program -> [Feature]
featuresOf (Program funcs stmts) = List.nub (concatMap funcFeatures funcs ++ fst (stmtListFeatures [] [] stmts))

funcFeatures :: Func -> [Feature]
funcFeatures func = UsesFunctionDecl : returnFeature ++ paramFeatures ++ bodyFeatures where
    returnFeature = if length (funcReturns func) > 1 then [UsesMultipleReturn] else []
    paramFeatures = concatMap (tyFeatures . fst) (funcParams func) ++ concatMap tyFeatures (funcReturns func)
    (bodyFeatures, _) = stmtListFeatures [] (map snd (funcParams func)) (funcBody func)

stmtListFeatures :: [[String]] -> [String] -> [Stmt] -> ([Feature], [String])
stmtListFeatures _ current [] = ([], current)
stmtListFeatures outers current (stmt : rest) = (features ++ restFeatures, finalCurrent) where
    (features, nextCurrent) = stmtFeatures outers current stmt
    (restFeatures, finalCurrent) = stmtListFeatures outers nextCurrent rest

stmtFeatures :: [[String]] -> [String] -> Stmt -> ([Feature], [String])
stmtFeatures outers current (SVar ty name expr) = (tyFeatures ty ++ exprFeatures expr ++ shadowFeatures outers current name, name : current)
stmtFeatures outers current (SVarZero ty name) = (UsesZeroInit : tyFeatures ty ++ shadowFeatures outers current name, name : current)
stmtFeatures _ current (STypeDecl _ ty) = (UsesTypeDecl : tyFeatures ty, current)
stmtFeatures outers current (SShortVar ty name expr) = (UsesShortVar : tyFeatures ty ++ exprFeatures expr ++ shadowFeatures outers current name, name : current)
stmtFeatures outers current (SShortVarCall vars _ args) = (UsesShortVar : UsesFunctionCall : callReturnFeature vars ++ concatMap (tyFeatures . fst) vars ++ concatMap exprFeatures args ++ concatMap (shadowFeatures outers current . snd) vars, map snd vars ++ current)
stmtFeatures _ current (SAssign _ expr) = (exprFeatures expr, current)
stmtFeatures _ current (SAssignCall _ _ args) = (UsesFunctionCall : concatMap exprFeatures args, current)
stmtFeatures _ current (SOpAssign _ _ expr) = (UsesCompoundAssign : exprFeatures expr, current)
stmtFeatures _ current (SIndexAssign target index expr) = (UsesIndex : exprFeatures target ++ exprFeatures index ++ exprFeatures expr, current)
stmtFeatures _ current (SDerefAssign target expr) = (UsesPointer : exprFeatures target ++ exprFeatures expr, current)
stmtFeatures outers current (SBlock stmts) = (UsesNestedBlock : features, current) where
    (features, _) = stmtListFeatures (current : outers) [] stmts
stmtFeatures outers current (SIf cond thn els) = (UsesIf : exprFeatures cond ++ thnFeatures ++ elsFeatures, current) where
    (thnFeatures, _) = stmtListFeatures (current : outers) [] thn
    (elsFeatures, _) = stmtListFeatures (current : outers) [] els
stmtFeatures outers current (SForBounded name _ body) = (UsesFor : shadowFeatures outers current name ++ bodyFeatures, current) where
    (bodyFeatures, _) = stmtListFeatures (current : outers) [name] body
stmtFeatures _ current (SPrintln exprs) = ((if length exprs > 1 then [UsesMultiplePrint] else []) ++ concatMap exprFeatures exprs, current)
stmtFeatures _ current (SExpr expr) = (exprFeatures expr, current)
stmtFeatures _ current (SBlank expr) = (exprFeatures expr, current)
stmtFeatures _ current (SReturn exprs) = ((if length exprs > 1 then [UsesMultipleReturn] else []) ++ concatMap exprFeatures exprs, current)

callReturnFeature :: [(Ty, String)] -> [Feature]
callReturnFeature vars = if length vars > 1 then [UsesMultipleReturn] else []

shadowFeatures :: [[String]] -> [String] -> String -> [Feature]
shadowFeatures outers current name
    | name `elem` concat (current : outers) = [UsesShadowing]
    | otherwise = []

exprFeatures :: Expr -> [Feature]
exprFeatures (EInt n)
    | n == 0 = [UsesZeroLiteral]
    | n < 0 = [UsesNegativeLiteral]
    | otherwise = []
exprFeatures (EBool _)
    = []
exprFeatures (EString _)
    = [UsesString]
exprFeatures (ENil ty)
    = tyFeatures ty
exprFeatures (EVar ty _)
    = tyFeatures ty
exprFeatures (EAdd lhs rhs)
    = both lhs rhs
exprFeatures (ESub lhs rhs)
    = both lhs rhs
exprFeatures (EMul lhs rhs)
    = both lhs rhs
exprFeatures (EDiv lhs rhs)
    = UsesDivision : both lhs rhs
exprFeatures (EMod lhs rhs)
    = UsesModulo : both lhs rhs
exprFeatures (EEq lhs rhs)
    = both lhs rhs
exprFeatures (ENe lhs rhs)
    = both lhs rhs
exprFeatures (ELt lhs rhs)
    = both lhs rhs
exprFeatures (ELe lhs rhs)
    = both lhs rhs
exprFeatures (EGt lhs rhs)
    = both lhs rhs
exprFeatures (EGe lhs rhs)
    = both lhs rhs
exprFeatures (ENot arg)
    = exprFeatures arg
exprFeatures (EAnd lhs rhs)
    = UsesShortCircuit : both lhs rhs
exprFeatures (EOr lhs rhs)
    = UsesShortCircuit : both lhs rhs
exprFeatures (EArrayLit ty exprs)
    = UsesArray : tyFeatures ty ++ concatMap exprFeatures exprs
exprFeatures (ESliceLit ty exprs)
    = UsesSlice : tyFeatures ty ++ concatMap exprFeatures exprs
exprFeatures (EStructLit ty fields)
    = UsesStruct : tyFeatures ty ++ concatMap (exprFeatures . snd) fields
exprFeatures (EIndex ty target index)
    = UsesIndex : tyFeatures ty ++ exprFeatures target ++ exprFeatures index
exprFeatures (EField ty target _)
    = UsesField : tyFeatures ty ++ exprFeatures target
exprFeatures (ELen expr)
    = exprFeatures expr
exprFeatures (ECall ty _ args)
    = UsesFunctionCall : tyFeatures ty ++ concatMap exprFeatures args
exprFeatures (EAddr expr)
    = UsesPointer : exprFeatures expr
exprFeatures (EDeref ty expr)
    = UsesPointer : tyFeatures ty ++ exprFeatures expr

both :: Expr -> Expr -> [Feature]
both lhs rhs = exprFeatures lhs ++ exprFeatures rhs

tyFeatures :: Ty -> [Feature]
tyFeatures TInt = []
tyFeatures TBool = []
tyFeatures TString = []
tyFeatures (TArray _ ty) = UsesArray : tyFeatures ty
tyFeatures (TSlice ty) = UsesSlice : tyFeatures ty
tyFeatures (TPointer ty) = UsesPointer : tyFeatures ty
tyFeatures (TNamed _) = []
tyFeatures (TStruct fields) = UsesStruct : concatMap (tyFeatures . fst) fields
