module Hol.ALPHA1.Back.BackEnd where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Show
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.Converter.Main
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Back.Runtime.Main
import Hol.ALPHA1.Back.Runtime.Util
import Hol.ALPHA1.Front.Analyzer.Main
import Hol.ALPHA1.Front.Desugarer.Main
import Hol.ALPHA1.Front.Header
import Hol.ALPHA1.Front.TypeChecker.Main
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Data.Char (toLower)
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.System.Shelly

isYES :: String -> Bool
isYES str = map toLower str `elem` ["y", "yes", "yes."]

answerView :: Context -> ([(LargeId, TermNode)], [Disagreement])
answerView final_ctx = (theAnswerSubst, theDisagreements) where
    namedBindings :: [(LargeId, TermNode)]
    namedBindings = [ (v, resolveBinding (_TotalVarBinding final_ctx) t) | (LV_Named v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx)) ]
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t = case viewNestedNAbs (rewrite NF t) of
        (n, t') -> case unfoldlNApp t' of
            (LVar v, ts)
                | ts == map mkNIdx [n, n - 1 .. 1] -> Just v
            _ -> Nothing
    isInternal :: LogicVar -> Bool
    isInternal (LV_Named _) = False
    isInternal _ = True
    renaming :: VarBinding
    renaming = VarBinding (Map.map (mkLVar . LV_Named) (Map.fromListWith min [ (w, v) | (v, t) <- namedBindings, Just w <- [tryMatchLVar t], isInternal w ]))
    theAnswerSubst :: [(LargeId, TermNode)]
    theAnswerSubst = [ (v, t') | (v, t) <- namedBindings, let t' = rewrite NF (applyBinding renaming t), tryMatchLVar t' /= Just (LV_Named v) ]
    theDisagreements :: [Disagreement]
    theDisagreements = applyBinding renaming (_LeftConstraints final_ctx)

runREPL :: Program TermNode -> UniqueGenT IO ()
runREPL program = lift (newIORef False) >>= go where
    myTabs :: String
    myTabs = ""
    promptify :: String -> IO String
    promptify str = shelly (moduleName program ++ "> " ++ str)
    mkRuntimeEnv :: TermNode -> IO RuntimeEnv
    mkRuntimeEnv query = return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer }) where
        runInteraction :: Context -> String -> IO Bool
        runInteraction ctx str = do
            isDebugging <- readIORef (_debuggindModeOn ctx)
            if isDebugging then do
                putStrLn str
                response <- promptify "Press the enter key to go to next state: "
                case response of
                    ":q" -> return False
                    ":d" -> do
                        writeIORef (_debuggindModeOn ctx) False
                        promptify "Debugging mode off for the rest of this query."
                        return True
                    _ -> return True
            else
                return True
        printAnswer :: Context -> IO RunMore
        printAnswer final_ctx
            | isShort && isClear = return False
            | isClear && List.null theAnswerSubst = return False
            | otherwise = do
                unless (List.null theAnswerSubst) $ do
                    promptify "The answer substitution is:"
                    sequence_ [ promptify (myTabs ++ v ++ " := " ++ shows t ".") | (v, t) <- theAnswerSubst ]
                unless isClear $ do
                    promptify "The remaining disagreements are:"
                    sequence_ [ promptify (myTabs ++ shows lhs (" =?= " ++ shows rhs ".")) | lhs :=?=: rhs <- theDisagreements ]
                askToRunMore
            where
                theAnswerSubst :: [(LargeId, TermNode)]
                theDisagreements :: [Disagreement]
                (theAnswerSubst, theDisagreements) = answerView final_ctx
                isShort :: Bool
                isShort = Set.null (getFreeLVs query)
                isClear :: Bool
                isClear = List.null theDisagreements
                askToRunMore :: IO RunMore
                askToRunMore = do
                    str <- promptify "Find more solutions? [Y/n] "
                    if List.null str
                        then askToRunMore
                        else return (isYES str)
    go :: IORef Debugging -> UniqueGenT IO ()
    go isDebugging = do
        query <- lift $ promptify ""
        case query of
            "" -> go isDebugging
            ":q" -> do
                lift $ shelly "hol >>= quit"
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
                            convertQuery used_mtvs assumptions (mkQueryFreeVariableEnv free_vars) query3
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                go isDebugging
                            Right query4 -> do
                                debugging_now <- lift (readIORef isDebugging >>= newIORef)
                                runtime_env <- lift $ mkRuntimeEnv query4
                                answer <- runExceptT (execRuntime runtime_env debugging_now (_FactDecls program) query4)
                                case answer of
                                    Left QuitRequested -> do
                                        lift $ shelly "hol >>= quit"
                                        return ()
                                    Left (BadGoalGiven _) -> do
                                        lift $ putStrLn "*** runtime-error: bad goal given!"
                                        go isDebugging
                                    Left (BadFactGiven _) -> do
                                        lift $ putStrLn "*** runtime-error: bad fact given!"
                                        go isDebugging
                                    Left (ArithmeticFailure err) -> do
                                        lift $ putStrLn ("*** runtime-error: " ++ shows err "")
                                        go isDebugging
                                    Right sat -> do
                                        lift $ promptify (if sat then "yes." else "no.")
                                        go isDebugging
                    Right _ -> do
                        lift $ putStrLn "*** parsing-error: it is not a query."
                        go isDebugging
