module Aladdin.Back.BackEnd where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Converter.Main
import Aladdin.Back.HOPU.Util
import Aladdin.Back.Runtime.Main
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Analyzer.Main
import Aladdin.Front.Desugarer.Main
import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Main
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit
import Z.System.Shelly
import Z.Utils

type Debugging = Bool

isYES :: String -> Bool
isYES str = str `elem` [ str1 ++ str2 ++ str3 | str1 <- ["Y", "y"], str2 <- ["", "es"], str3 <- if null str2 then [""] else ["", "."] ]

eraseTrivialBinding :: LVarSubst -> LVarSubst
eraseTrivialBinding = VarBinding . loop . unVarBinding where
    hasName :: LogicVar -> Bool
    hasName (LV_Named _) = True
    hasName _ = False
    loop :: Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    loop = foldr go <*> Map.toAscList
    go :: (LogicVar, TermNode) -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    go (v, t) = maybe id (dispatch v) (tryMatchLVar t)
    dispatch :: LogicVar -> LogicVar -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    dispatch v1 v2
        | v1 == v2 = loop . Map.delete v1
        | hasName v1 && not (hasName v2) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v2 (LVar v1) })) . Map.delete v2
        | not (hasName v1) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v1 (LVar v2) })) . Map.delete v1
        | otherwise = id
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t
        = case viewNestedNAbs (rewrite NF t) of
            (n, t') -> case unfoldlNApp t' of
                (LVar v, ts) -> if ts == map mkNIdx [1 .. n] then Just v else Nothing
                _ -> Nothing

runREPL :: Program TermNode -> UniqueGenT IO ()
runREPL program = lift (newIORef False) >>= go where
    myTabs :: String
    myTabs = ""
    promptify :: String -> IO String
    promptify str = shelly (moduleName program ++ "> " ++ str)
    mkRuntimeEnv :: IORef Debugging -> TermNode -> IO RuntimeEnv
    mkRuntimeEnv isDebugging query = return (RuntimeEnv { _PutStr = runInteraction, _Answer = printAnswer }) where
        runInteraction :: String -> IO ()
        runInteraction str = do
            debugging <- readIORef isDebugging
            when debugging $ do
                putStrLn str
                response <- promptify "Press the enter key to go to next state: "
                case response of
                    ":q" -> do
                        shelly "Aladdin >>= quit"
                        exitSuccess
                    ":d" -> do
                        modifyIORef isDebugging not
                        debugging <- readIORef isDebugging
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
            | otherwise = do
                printDisagreements
                askToRunMore
            where
                theAnswerSubst :: [(LargeId, TermNode)]
                theAnswerSubst = [ (v, t) | (LV_Named v, t) <- Map.toList (unVarBinding (eraseTrivialBinding (_TotalVarBinding final_ctx))) ]
                isShort :: Bool
                isShort = Set.null (getFreeLVs query)
                isClear :: Bool
                isClear = List.null (_LeftConstraints final_ctx)
                askToRunMore :: IO RunMore
                askToRunMore = do
                    str <- promptify "Find more solutions? [Y/n] "
                    if List.null str
                        then askToRunMore
                        else return (isYES str)
                printDisagreements :: IO ()
                printDisagreements = do
                    promptify "The remaining disagreements are:"
                    sequence_
                        [ promptify (myTabs ++ shows lhs (" =?= " ++ shows rhs "."))
                        | lhs :=?=: rhs <- _LeftConstraints final_ctx
                        ]
                    promptify "The binding is:"
                    sequence_
                        [ promptify (myTabs ++ shows (mkLVar v) (" := " ++ shows t "."))
                        | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding final_ctx))
                        ]
    go :: IORef Debugging -> UniqueGenT IO ()
    go isDebugging = do
        query <- lift $ promptify ""
        case query of
            "" -> do
                lift $ shelly "Aladdin >>= quit"
                return ()
            ":q" -> do
                lift $ shelly "Aladdin >>= quit"
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
                                answer <- runExceptT (execRuntime runtime_env (_FactDecls program) query4)
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
