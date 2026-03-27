module ALPHA2.Main where

import ALPHA2.Compiler
import ALPHA2.Constant
import ALPHA2.Desugarer
import ALPHA2.Header
import ALPHA2.HOPU
import ALPHA2.PlanHolLexer
import ALPHA2.PlanHolParser
import ALPHA2.Runtime
import ALPHA2.TermNode
import ALPHA2.TypeChecker
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Maybe
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO
import Z.System
import Z.Utils

type AnalyzerOuput = Either TermRep [DeclRep]

runAnalyzer :: String -> Either ErrMsg AnalyzerOuput
runAnalyzer src0
    = case runHolLexer src0 of
        Left (row, col) -> Left ("*** lexing error at { row = " ++ showsPrec 0 row (", col = " ++ showsPrec 0 col " }."))
        Right src1 -> case runHolParser src1 of
            Left Nothing -> Left ("*** parsing error at EOF.")
            Left (Just token) -> case getSLoc token of
                SLoc (row1, col1) (row2, col2) -> Left ("*** parsing error at { row = " ++ showsPrec 0 row1 (", col = " ++ showsPrec 0 col1 " }."))
            Right output -> Right output

isYES :: String -> Bool
isYES str = str `elem` [ str1 ++ str2 ++ str3 | str1 <- ["Y", "y"], str2 <- ["", "es"], str3 <- if null str2 then [""] else ["", "."] ]

addIndex :: Fact -> (Constant, Fact)
addIndex fact = (hd fact', fact') where
    fact' :: Fact
    fact' = rewrite NF fact
    hd :: Fact -> Constant
    hd t = case unfoldlNApp t of
        (NLam t, _) -> hd t
        (NCon (DC (DC_LO LO_ty_pi)), [t]) -> hd t
        (NCon (DC (DC_LO LO_pi)), [t]) -> hd t
        (NCon (DC (DC_LO LO_if)), [t, _]) -> hd t
        (NCon c, _) -> c

execRuntime :: RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr (UniqueT IO) Satisfied
execRuntime env isDebugging facts query = do
    call_id <- getUnique
    let initialContext = Context { _TotalVarBinding = mempty, _CurrentLabeling = Labeling { _ConLabel = Map.empty, _VarLabel = Map.fromSet (const 0) (getLVars query) }, _LeftConstraints = [], _ContextThreadId = call_id, _debuggindModeOn = isDebugging }
    runTransition env (getLVars query) [(initialContext, [Cell { _GivenFacts = map addIndex facts, _GivenHypos = [], _ScopeLevel = 0, _WantedGoal = query, _CellCallId = call_id }])]

runREPL :: Program TermNode -> UniqueT IO ()
runREPL program = lift (newIORef False) >>= go where
    myTabs :: String
    myTabs = ""
    promptify :: String -> IO String
    promptify str = shelly (moduleName program ++ "> " ++ str)
    mkRuntimeEnv :: IORef Debugging -> TermNode -> IO RuntimeEnv
    mkRuntimeEnv isDebugging query = return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer }) where
        runInteraction :: Context -> String -> IO ()
        runInteraction ctx str = do
            isDebugging <- readIORef (_debuggindModeOn ctx)
            when isDebugging $ do
                putStrLn str
                response <- promptify "Press the enter key to go to next state: "
                case response of
                    ":d" -> do
                        modifyIORef (_debuggindModeOn ctx) not
                        debugging <- readIORef (_debuggindModeOn ctx)
                        promptify "Debugging mode off."
                        return ()
                    _ -> return ()
        printAnswer :: Context -> IO RunMore
        printAnswer final_ctx
            | isShort && isClear = return False
            | isClear && List.null theAnswerSubst = return False
            | isClear = do
                promptify "The answer substitution is:"
                sequence_
                    [ promptify (myTabs ++ v ++ " := " ++ shows t ".")
                    | (v, t) <- theAnswerSubst
                    ]
                askToRunMore
            | not consistent = return True
            | otherwise = do
                printDisagreements
                askToRunMore
            where
                theAnswerSubst :: [(LargeId, TermNode)]
                theAnswerSubst = [ (v, t) | (LV_Named v, t) <- Map.toList (unVarBinding (eraseTrivialBinding (_TotalVarBinding final_ctx))) ]
                isShort :: Bool
                isShort = Set.null (getLVars query)
                isClear :: Bool
                isClear = List.null (_LeftConstraints final_ctx)
                askToRunMore :: IO RunMore
                askToRunMore = do
                    str <- promptify "Find more solutions? [Y/n] "
                    if List.null str then askToRunMore else return (isYES str)
                printDisagreements :: IO ()
                printDisagreements = do
                    promptify "The remaining constraints are:"
                    sequence_
                        [ promptify (myTabs ++ shows constraint "")
                        | constraint <- _LeftConstraints final_ctx
                        ]
                    promptify "The binding is:"
                    sequence_
                        [ promptify (myTabs ++ shows (mkLVar v) (" := " ++ shows t "."))
                        | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))
                        ]
                evalokay :: Bool
                evalokay = and
                    [ case (evaluateA lhs, evaluateA rhs) of
                        (Right x, Right y) -> x == y
                        _ -> False 
                    | EvalutionConstraint lhs rhs <- _LeftConstraints final_ctx
                    ]
                arithokay :: Bool
                arithokay = and
                    [ case evaluateB b of
                        Right b -> b
                        _ -> False
                    | ArithmeticConstraint b <- _LeftConstraints final_ctx
                    ]
                consistent :: Bool
                consistent = evalokay && arithokay 
    go :: IORef Debugging -> UniqueT IO ()
    go isDebugging = do
        query <- lift $ promptify ""
        case query of
            "" -> do
                lift $ shelly "Hol >>= quit"
                return ()
            ":q" -> do
                lift $ shelly "Hol >>= quit"
                return ()
            ":d" -> do
                lift $ do
                    modifyIORef isDebugging not
                    debugging <- readIORef isDebugging
                    promptify ("Debugging mode " ++ (if debugging then "on" else "off") ++ ".")
                go isDebugging
            query0 -> case runAnalyzer query0 of
                Left err_msg -> do
                    lift $ putStrLn err_msg
                    go isDebugging
                Right output -> case output of
                    Left query1 -> do
                        result <- runExceptT $ do
                            (query2, free_vars) <- desugarQuery query1
                            (query3, (used_mtvs, assumptions)) <- checkType (_TypeDecls program) query2 mkTyO
                            convertQuery used_mtvs assumptions (Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList free_vars ]) query3
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                go isDebugging
                            Right query4 -> do
                                runtime_env <- lift $ mkRuntimeEnv isDebugging query4
                                answer <- runExceptT (execRuntime runtime_env isDebugging (_FactDecls program) query4)
                                case answer of
                                    Left runtime_err -> case runtime_err of
                                        BadGoalGiven _ -> lift $ putStrLn "*** runtime-error: bad goal given!"
                                        BadFactGiven _ -> lift $ putStrLn "*** runtime-error: bad fact given!"
                                    Right sat -> do
                                        lift $ promptify (if sat then "yes." else "no.")
                                        return ()
                                go isDebugging
                    Right src1 -> do
                        lift $ putStrLn "*** parsing-error: it is not a query."
                        go isDebugging

theInitialKindDecls :: KindEnv
theInitialKindDecls = Map.fromList
    [ (TC_Arrow, read "* -> * -> *")
    , (TC_Named "list", read "* -> *")
    , (TC_Named "o", read "*")
    , (TC_Named "char", read "*")
    , (TC_Named "nat", read "*")
    , (TC_Named "string", read "*")
    ]

theInitialTypeDecls :: TypeEnv
theInitialTypeDecls = Map.fromList
    [ (DC_LO LO_if, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_and, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_or, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_imply, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_sigma, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_pi, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_cut, Forall [] (mkTyO))
    , (DC_LO LO_true, Forall [] (mkTyO))
    , (DC_LO LO_fail, Forall [] (mkTyO))
    , (DC_LO LO_is, Forall ["A"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    , (DC_LO LO_debug, Forall [] (mkTyList mkTyChr `mkTyArrow` mkTyO))
    , (DC_Nil, Forall ["A"] (mkTyList (TyVar 0)))
    , (DC_Cons, Forall ["A"] (TyVar 0 `mkTyArrow` (mkTyList (TyVar 0) `mkTyArrow` mkTyList (TyVar 0))))
    , (DC_Succ, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_eq, Forall ["A"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    , (DC_ge, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_gt, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_le, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_lt, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_plus, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_minus, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_mul, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_div, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    ]

theInitialFactDecls :: [TermNode]
theInitialFactDecls = [eqFact] where
    eqFact :: TermNode
    eqFact = mkNApp (mkNCon LO_ty_pi) (mkNLam (mkNApp (mkNCon LO_pi) (mkNLam (mkNApp (mkNApp (mkNApp (mkNCon DC_eq) (mkNIdx 1)) (mkNIdx 0)) (mkNIdx 0)))))

theDefaultModuleName :: String
theDefaultModuleName = "Hol"

runHol :: UniqueT IO ()
runHol = do
    consistency_ptr <- lift $ newIORef ""
    file_dir <- lift $ shelly "Hol =<< "
    maybe_file_name <- case matchFileDirWithExtension file_dir of
        ("", "") -> return Nothing
        (file_name, ".hol") -> return (Just file_name)
        (file_name, "") -> return (Just file_name)
        (file_name, '.' : wrong_extension) -> do
            lift $ writeIORef consistency_ptr (theDefaultModuleName ++ "> " ++ shows wrong_extension " is a non-executable file extension.")
            return Nothing
    consistency <- lift $ readIORef consistency_ptr
    case consistency of
        "" -> case maybe_file_name of
            Nothing -> do
                lift $ shelly (theDefaultModuleName ++ "> Ok, no module loaded.")
                runREPL (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName })
            Just file_name -> do
                let my_file_dir = file_name ++ ".hol"
                    myModuleName = modifySep '/' (const ".") id file_name
                src <- lift $ readFile my_file_dir
                file_abs_dir <- fmap (fromMaybe my_file_dir) (lift $ makePathAbsolutely my_file_dir)
                lift $ shelly (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", interpreted )")
                case runAnalyzer src of
                    Left err_msg -> do
                        lift $ putStrLn err_msg
                        runHol
                    Right output -> case output of
                        Left query1 -> do
                            lift $ putStrLn "*** parsing-error: it is not a program."
                            runHol
                        Right program1 -> do
                            result <- runExceptT $ do
                                module1 <- desugarProgram theInitialKindDecls theInitialTypeDecls theDefaultModuleName program1
                                facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                                facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                                return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = theInitialFactDecls ++ facts3, moduleName = myModuleName })
                            case result of
                                Left err_msg -> do
                                    lift $ putStrLn err_msg
                                    runHol
                                Right program2 -> do
                                    lift $ shelly (myModuleName ++ "> Ok, one module loaded.")
                                    runREPL program2
        inconsistent_proof -> do
            lift $ shelly inconsistent_proof
            lift $ shelly ("Hol >>= quit")
            return ()

main :: IO ()
main = do
    runStateT (runUniqueT runHol) 0
    return ()
