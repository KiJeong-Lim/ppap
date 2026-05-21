module Project.A.Go.Pretty where

import Project.A.Go.AST
import Z.Utils

prettyProgram :: Program -> String
prettyProgram = withZero . showProgram

prettyStmt :: Int -> Stmt -> [String]
prettyStmt depth stmt
    = case stmt of
        SVar ty name expr -> [indent depth ++ "var " ++ name ++ " " ++ prettyTy ty ++ " = " ++ prettyExpr expr]
        SVarZero ty name -> [indent depth ++ "var " ++ name ++ " " ++ prettyTy ty]
        STypeDecl name ty -> prettyTypeDecl depth name ty
        SShortVar _ name expr -> [indent depth ++ name ++ " := " ++ prettyExpr expr]
        SShortVarCall vars name args -> [indent depth ++ comma (map snd vars) ++ " := " ++ name ++ "(" ++ comma (map prettyExpr args) ++ ")"]
        SAssign name expr -> [indent depth ++ name ++ " = " ++ prettyExpr expr]
        SAssignCall names name args -> [indent depth ++ comma names ++ " = " ++ name ++ "(" ++ comma (map prettyExpr args) ++ ")"]
        SOpAssign name op expr -> [indent depth ++ name ++ " " ++ op ++ " " ++ prettyExpr expr]
        SIndexAssign target index expr -> [indent depth ++ prettyExpr target ++ "[" ++ prettyExpr index ++ "] = " ++ prettyExpr expr]
        SDerefAssign target expr -> [indent depth ++ "*" ++ prettyExprPrec 7 target ++ " = " ++ prettyExpr expr]
        SBlock stmts -> [indent depth ++ "{"] ++ concatMap (prettyStmt (depth + 1)) stmts ++ [indent depth ++ "}"]
        SIf cond thn els -> concat
            [ [indent depth ++ "if " ++ prettyExpr cond ++ " {"]
            , concatMap (prettyStmt (depth + 1)) thn
            , if null els then [indent depth ++ "}"] else [indent depth ++ "} else {"] ++ concatMap (prettyStmt (depth + 1)) els ++ [indent depth ++ "}"]
            ]
        SForBounded name bound body -> [indent depth ++ "for " ++ name ++ " := 0; " ++ name ++ " < " ++ show bound ++ "; " ++ name ++ "++ {"] ++ concatMap (prettyStmt (depth + 1)) body ++ [indent depth ++ "}"]
        SPrintln exprs -> [indent depth ++ "fmt.Println(" ++ comma (map prettyExpr exprs) ++ ")"]
        SExpr expr -> [indent depth ++ prettyExpr expr]
        SBlank expr -> [indent depth ++ "_ = " ++ prettyExpr expr]
        SReturn exprs -> [indent depth ++ "return " ++ comma (map prettyExpr exprs)]

prettyTy :: Ty -> String
prettyTy = withZero . showTy

prettyExpr :: Expr -> String
prettyExpr = withZero . showExpr 0

prettyExprPrec :: Int -> Expr -> String
prettyExprPrec prec = withZero . showExpr prec

prettyTypeDecl :: Int -> String -> Ty -> [String]
prettyTypeDecl depth name (TStruct fields) =
    [indent depth ++ "type " ++ name ++ " struct {"] ++ map (prettyFieldDecl (depth + 1)) fields ++ [indent depth ++ "}"]
prettyTypeDecl depth name ty = [indent depth ++ "type " ++ name ++ " " ++ prettyTy ty]

prettyFieldDecl :: Int -> (Ty, String) -> String
prettyFieldDecl depth (ty, name) = indent depth ++ name ++ " " ++ prettyTy ty

showProgram :: Program -> ShowS
showProgram (Program funcs stmts) = strcat
    [ strstr "package main" . nl
    , nl
    , strstr "import \"fmt\"" . nl
    , nl
    , strcat [ showFunc func . nl | func <- funcs ]
    , strstr "func main() {" . nl
    , strcat [ strstr line . nl | stmt <- stmts, line <- prettyStmt 1 stmt ]
    , strstr "}" . nl
    ]

showFunc :: Func -> ShowS
showFunc func = strcat
    [ strstr "func "
    , strstr (funcName func)
    , strstr "("
    , strstr (comma (map prettyParam (funcParams func)))
    , strstr ")"
    , showReturns (funcReturns func)
    , strstr " {"
    , nl
    , strcat [strstr line . nl | stmt <- funcBody func, line <- prettyStmt 1 stmt]
    , strstr "}"
    , nl
    ]

prettyParam :: (Ty, String) -> String
prettyParam (ty, name) = name ++ " " ++ prettyTy ty

showReturns :: [Ty] -> ShowS
showReturns [] = id
showReturns [ty] = strstr " " . showTy ty
showReturns tys = strstr " (" . strstr (comma (map prettyTy tys)) . strstr ")"

showTy :: Ty -> ShowS
showTy TInt = strstr "int"
showTy TBool = strstr "bool"
showTy TString = strstr "string"
showTy (TArray n ty) = strstr "[" . shows n . strstr "]" . showTy ty
showTy (TSlice ty) = strstr "[]" . showTy ty
showTy (TPointer ty) = strstr "*" . showTy ty
showTy (TNamed name) = strstr name
showTy (TStruct fields) = strstr "struct {" . showStructFields fields . strstr " }"

showStructFields :: [(Ty, String)] -> ShowS
showStructFields [] = id
showStructFields fields = strstr " " . strstr (semi (map prettyField fields))

prettyField :: (Ty, String) -> String
prettyField (ty, name) = name ++ " " ++ prettyTy ty

showExpr :: Int -> Expr -> ShowS
showExpr _ (EInt n) = shows n
showExpr _ (EBool True) = strstr "true"
showExpr _ (EBool False) = strstr "false"
showExpr _ (EString str) = showGoStringLit str
showExpr _ (ENil _) = strstr "nil"
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
showExpr _ (EArrayLit ty exprs) = showTy (TArray (length exprs) ty) . strstr "{" . strstr (comma (map prettyExpr exprs)) . strstr "}"
showExpr _ (ESliceLit ty exprs) = showTy (TSlice ty) . strstr "{" . strstr (comma (map prettyExpr exprs)) . strstr "}"
showExpr _ (EStructLit ty fields) = showTy ty . strstr "{" . strstr (comma (map prettyStructLitField fields)) . strstr "}"
showExpr prec (EIndex _ target index) = showParenIf (prec > 8) (showExpr 8 target . strstr "[" . showExpr 0 index . strstr "]")
showExpr prec (EField _ target name) = showParenIf (prec > 8) (showExpr 8 target . strstr "." . strstr name)
showExpr _ (ELen expr) = strstr "len(" . showExpr 0 expr . strstr ")"
showExpr _ (ECall _ name args) = strstr name . strstr "(" . strstr (comma (map prettyExpr args)) . strstr ")"
showExpr prec (EAddr expr) = showParenIf (prec > 7) (strstr "&" . showExpr 7 expr)
showExpr prec (EDeref _ expr) = showParenIf (prec > 7) (strstr "*" . showExpr 7 expr)

prettyStructLitField :: (String, Expr) -> String
prettyStructLitField (name, expr) = name ++ ": " ++ prettyExpr expr

showGoStringLit :: String -> ShowS
showGoStringLit str = strstr "\"" . strcat (map showGoEscapedChar str) . strstr "\""

showGoEscapedChar :: Char -> ShowS
showGoEscapedChar '\"' = strstr "\\\""
showGoEscapedChar '\\' = strstr "\\\\"
showGoEscapedChar '\n' = strstr "\\n"
showGoEscapedChar '\r' = strstr "\\r"
showGoEscapedChar '\t' = strstr "\\t"
showGoEscapedChar ch = if ch < ' ' then strstr "\\x" . showHex2 (fromEnum ch) else strstr [ch]

showHex2 :: Int -> ShowS
showHex2 n = strstr [digit 16, digit 1] where
    digit :: Int -> Char
    digit k = "0123456789abcdef" !! ((n `div` k) `mod` 16)

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

semi :: [String] -> String
semi [] = ""
semi [x] = x
semi (x : xs) = x ++ concatMap ("; " ++) xs
