module Project.A.Go.Pretty
    ( prettyProgram
    , prettyExpr
    , prettyStmt
    , prettyTy
    ) where

import Project.A.Go.AST

prettyProgram :: Program -> String
prettyProgram (Program stmts) =
    unlines $
        [ "package main"
        , ""
        , "import \"fmt\""
        , ""
        , "func main() {"
        ]
            ++ concatMap (prettyStmt 1) stmts
            ++ [ "}" ]

prettyStmt :: Int -> Stmt -> [String]
prettyStmt depth stmt =
    case stmt of
        SVar ty name expr ->
            [indent depth ++ "var " ++ name ++ " " ++ prettyTy ty ++ " = " ++ prettyExpr expr]
        SAssign name expr ->
            [indent depth ++ name ++ " = " ++ prettyExpr expr]
        SBlock stmts ->
            [indent depth ++ "{"] ++ concatMap (prettyStmt (depth + 1)) stmts ++ [indent depth ++ "}"]
        SIf cond thn els ->
            [indent depth ++ "if " ++ prettyExpr cond ++ " {"]
                ++ concatMap (prettyStmt (depth + 1)) thn
                ++ if null els
                    then [indent depth ++ "}"]
                    else [indent depth ++ "} else {"] ++ concatMap (prettyStmt (depth + 1)) els ++ [indent depth ++ "}"]
        SForBounded name bound body ->
            [indent depth ++ "for " ++ name ++ " := 0; " ++ name ++ " < " ++ show bound ++ "; " ++ name ++ "++ {"]
                ++ concatMap (prettyStmt (depth + 1)) body
                ++ [indent depth ++ "}"]
        SPrintln exprs ->
            [indent depth ++ "fmt.Println(" ++ comma (map prettyExpr exprs) ++ ")"]

prettyTy :: Ty -> String
prettyTy ty =
    case ty of
        TInt -> "int"
        TBool -> "bool"
        TString -> "string"

prettyExpr :: Expr -> String
prettyExpr = prettyExprPrec 0

prettyExprPrec :: Int -> Expr -> String
prettyExprPrec prec expr =
    case expr of
        EInt n -> show n
        EBool True -> "true"
        EBool False -> "false"
        EString str -> show str
        EVar _ name -> name
        EAdd lhs rhs -> bin 5 "+" lhs rhs
        ESub lhs rhs -> bin 5 "-" lhs rhs
        EMul lhs rhs -> bin 6 "*" lhs rhs
        EDiv lhs rhs -> bin 6 "/" lhs rhs
        EMod lhs rhs -> bin 6 "%" lhs rhs
        EEq lhs rhs -> bin 3 "==" lhs rhs
        ENe lhs rhs -> bin 3 "!=" lhs rhs
        ELt lhs rhs -> bin 3 "<" lhs rhs
        ELe lhs rhs -> bin 3 "<=" lhs rhs
        EGt lhs rhs -> bin 3 ">" lhs rhs
        EGe lhs rhs -> bin 3 ">=" lhs rhs
        ENot arg -> paren (prec > 7) ("!" ++ prettyExprPrec 7 arg)
        EAnd lhs rhs -> bin 2 "&&" lhs rhs
        EOr lhs rhs -> bin 1 "||" lhs rhs
  where
    bin myPrec op lhs rhs =
        paren (prec > myPrec) $
            prettyExprPrec myPrec lhs ++ " " ++ op ++ " " ++ prettyExprPrec (myPrec + 1) rhs

paren :: Bool -> String -> String
paren True str = "(" ++ str ++ ")"
paren False str = str

indent :: Int -> String
indent depth = replicate (4 * depth) ' '

comma :: [String] -> String
comma [] = ""
comma [x] = x
comma (x : xs) = x ++ concatMap (", " ++) xs
