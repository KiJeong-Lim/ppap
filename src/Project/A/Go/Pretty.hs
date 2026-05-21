module Project.A.Go.Pretty where

import Project.A.Go.AST
import Z.Utils

prettyProgram :: Program -> String
prettyProgram = withZero . showProgram

prettyStmt :: Int -> Stmt -> [String]
prettyStmt depth stmt
    = case stmt of
        SVar ty name expr -> [indent depth ++ "var " ++ name ++ " " ++ prettyTy ty ++ " = " ++ prettyExpr expr]
        SAssign name expr -> [indent depth ++ name ++ " = " ++ prettyExpr expr]
        SBlock stmts -> [indent depth ++ "{"] ++ concatMap (prettyStmt (depth + 1)) stmts ++ [indent depth ++ "}"]
        SIf cond thn els -> concat
            [ [indent depth ++ "if " ++ prettyExpr cond ++ " {"]
            , concatMap (prettyStmt (depth + 1)) thn
            , if null els then [indent depth ++ "}"] else [indent depth ++ "} else {"] ++ concatMap (prettyStmt (depth + 1)) els ++ [indent depth ++ "}"]
            ]
        SForBounded name bound body -> [indent depth ++ "for " ++ name ++ " := 0; " ++ name ++ " < " ++ show bound ++ "; " ++ name ++ "++ {"] ++ concatMap (prettyStmt (depth + 1)) body ++ [indent depth ++ "}"]
        SPrintln exprs -> [indent depth ++ "fmt.Println(" ++ comma (map prettyExpr exprs) ++ ")"]

prettyTy :: Ty -> String
prettyTy = withZero . showTy

prettyExpr :: Expr -> String
prettyExpr = withZero . showExpr 0

prettyExprPrec :: Int -> Expr -> String
prettyExprPrec prec = withZero . showExpr prec

showProgram :: Program -> ShowS
showProgram (Program stmts) = strcat
    [ strstr "package main" . nl
    , nl
    , strstr "import \"fmt\"" . nl
    , nl
    , strstr "func main() {" . nl
    , strcat [ strstr line . nl | stmt <- stmts, line <- prettyStmt 1 stmt ]
    , strstr "}" . nl
    ]

showTy :: Ty -> ShowS
showTy TInt = strstr "int"
showTy TBool = strstr "bool"
showTy TString = strstr "string"

showExpr :: Int -> Expr -> ShowS
showExpr _ (EInt n) = shows n
showExpr _ (EBool True) = strstr "true"
showExpr _ (EBool False) = strstr "false"
showExpr _ (EString str) = shows str
showExpr _ (EVar _ name) = strstr name
showExpr prec (EAdd lhs rhs) = showBin prec 5 "+" lhs rhs
showExpr prec (ESub lhs rhs) = showBin prec 5 "-" lhs rhs
showExpr prec (EMul lhs rhs) = showBin prec 6 "*" lhs rhs
showExpr prec (EDiv lhs rhs) = showBin prec 6 "/" lhs rhs
showExpr prec (EMod lhs rhs) = showBin prec 6 "%" lhs rhs
showExpr prec (EEq lhs rhs) = showBin prec 3 "==" lhs rhs
showExpr prec (ENe lhs rhs) = showBin prec 3 "!=" lhs rhs
showExpr prec (ELt lhs rhs) = showBin prec 3 "<" lhs rhs
showExpr prec (ELe lhs rhs) = showBin prec 3 "<=" lhs rhs
showExpr prec (EGt lhs rhs) = showBin prec 3 ">" lhs rhs
showExpr prec (EGe lhs rhs) = showBin prec 3 ">=" lhs rhs
showExpr prec (ENot arg) = showParenIf (prec > 7) (strstr "!" . showExpr 7 arg)
showExpr prec (EAnd lhs rhs) = showBin prec 2 "&&" lhs rhs
showExpr prec (EOr lhs rhs) = showBin prec 1 "||" lhs rhs

showBin :: Int -> Int -> String -> Expr -> Expr -> ShowS
showBin prec my_prec op lhs rhs = showParenIf (prec > my_prec) (showExpr my_prec lhs . strstr " " . strstr op . strstr " " . showExpr (my_prec + 1) rhs)

showParenIf :: Bool -> ShowS -> ShowS
showParenIf True delta = strstr "(" . delta . strstr ")"
showParenIf False delta = delta

indent :: Int -> String
indent depth = replicate (4 * depth) ' '

comma :: [String] -> String
comma [] = ""
comma [x] = x
comma (x : xs) = x ++ concatMap (", " ++) xs
