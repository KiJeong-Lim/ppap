module Hol.ALPHA2.Runtime where

import Hol.ALPHA2.TermNode
import Hol.ALPHA2.HOPU
import Hol.ALPHA2.Constant
import Hol.ALPHA2.Header
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Maybe
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

type CallId = Unique

type Debugging = Bool

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    deriving ()

data Constraint
    = DisagreementConstraint Disagreement
    | EvalutionConstraint TermNode TermNode
    | DefinedConstraint TermNode
    | ArithmeticConstraint !(TermNode)
    deriving ()

assertConstraint :: Constraint -> ()
assertConstraint constraint = case constraint of
    DisagreementConstraint (lhs :=?=: rhs) ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    EvalutionConstraint lhs rhs ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    DefinedConstraint term -> assertNonnegativeIndices term
    ArithmeticConstraint term -> assertNonnegativeIndices term

assertConstraints :: [Constraint] -> ()
assertConstraints [] = ()
assertConstraints (constraint : rest) = assertConstraint constraint `seq` assertConstraints rest

instance Eq Constraint where
    lhs == rhs
        = assertConstraint lhs `seq`
          assertConstraint rhs `seq`
          case (lhs, rhs) of
            (DisagreementConstraint d1, DisagreementConstraint d2) -> d1 == d2
            (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> l1 == l2 && r1 == r2
            (DefinedConstraint t1, DefinedConstraint t2) -> t1 == t2
            (ArithmeticConstraint t1, ArithmeticConstraint t2) -> t1 == t2
            _ -> False

instance Ord Constraint where
    compare lhs rhs
        = assertConstraint lhs `seq`
          assertConstraint rhs `seq`
          case (lhs, rhs) of
            (DisagreementConstraint d1, DisagreementConstraint d2) -> compare d1 d2
            (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> compare l1 l2 <> compare r1 r2
            (DefinedConstraint t1, DefinedConstraint t2) -> compare t1 t2
            (ArithmeticConstraint t1, ArithmeticConstraint t2) -> compare t1 t2
            _ -> compare (constraintTag lhs) (constraintTag rhs)
      where
        constraintTag (DisagreementConstraint _) = 0 :: Int
        constraintTag (EvalutionConstraint _ _) = 1
        constraintTag (DefinedConstraint _) = 2
        constraintTag (ArithmeticConstraint _) = 3

data Cell
    = Cell
        { _GivenFacts :: Map.Map Constant [Fact]
        , _GivenHypos :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _CellCallId :: CallId
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Constraint]
        , _ContextThreadId :: CallId
        , _debuggindModeOn :: IORef Debugging
        }
    deriving ()

assertCell :: Cell -> ()
assertCell cell
    | _ScopeLevel cell < 0 = undefined
    | otherwise =
        assertNonnegativeTerms (concat (Map.elems (_GivenFacts cell))) `seq`
        assertNonnegativeTerms [ NCon constant | constant <- Map.keys (_GivenFacts cell) ] `seq`
        assertNonnegativeTerms (_GivenHypos cell) `seq`
        assertNonnegativeIndices (_WantedGoal cell)

assertContext :: Context -> ()
assertContext ctx
    = assertVarBinding (_TotalVarBinding ctx) `seq`
      assertLabelingDomain (_CurrentLabeling ctx) `seq`
      assertConstraints (_LeftConstraints ctx)

assertLabelingDomain :: Labeling -> ()
assertLabelingDomain labeling
    = assertScopeMap (_ConLabel labeling) `seq`
      assertScopeMap (_VarLabel labeling)
  where
    assertScopeMap values = IntMap.foldrWithKey
        (\key level rest -> if key < 0 || level < 0 then undefined else rest)
        () values

assertStack :: Stack -> ()
assertStack [] = ()
assertStack ((ctx, cells) : rest)
    = assertContext ctx `seq` assertCells cells `seq` assertStack rest
  where
    assertCells [] = ()
    assertCells (cell : more) = assertCell cell `seq` assertCells more

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: Context -> String -> IO ()
        , _Answer :: Context -> IO RunMore
        }
    deriving ()

instance ZonkLVar Context where
    zonkLVar theta ctx
        = assertVarBinding theta `seq`
          assertVarBinding (_TotalVarBinding ctx) `seq`
          assertConstraints (_LeftConstraints ctx) `seq`
          Context
        { _TotalVarBinding = theta <> _TotalVarBinding ctx
        , _CurrentLabeling = zonkLVar theta (_CurrentLabeling ctx)
        , _LeftConstraints = zonkLVar theta (_LeftConstraints ctx)
        , _ContextThreadId = _ContextThreadId ctx
        , _debuggindModeOn = _debuggindModeOn ctx
        }

instance ZonkLVar Constraint where
    zonkLVar theta constraint
        = assertVarBinding theta `seq`
          assertConstraint constraint `seq`
          go constraint
      where
        go (DisagreementConstraint eqn)
            = DisagreementConstraint (bindVars theta eqn)
        go (EvalutionConstraint lhs rhs)
            = EvalutionConstraint (bindVars theta lhs) (bindVars theta rhs)
        go (DefinedConstraint term)
            = DefinedConstraint (bindVars theta term)
        go (ArithmeticConstraint arith)
            = ArithmeticConstraint (bindVars theta arith)

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts hyps level goal call_id)
        = assertVarBinding theta `seq`
          assertNonnegativeTerms (concat (Map.elems facts)) `seq`
          assertNonnegativeTerms hyps `seq`
          assertNonnegativeIndices goal `seq`
          mkCell facts (bindVars theta hyps) level (bindVars theta goal) call_id

instance Show Constraint where
    showsPrec prec (DisagreementConstraint eqn) = showsPrec prec eqn
    showsPrec prec (EvalutionConstraint lhs rhs) = showsPrec prec lhs . strstr " is " . showsPrec prec rhs
    showsPrec prec (DefinedConstraint term) = strstr "defined(" . showsPrec prec term . strstr ")"
    showsPrec prec (ArithmeticConstraint arith) = showsPrec prec arith

mkCell :: Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts hyps level goal call_id = goal `seq` Cell { _GivenFacts = facts, _GivenHypos = hyps, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showsvdash :: Show goal => Indentation -> [Fact] -> goal -> ShowS
showsvdash space [] goal = strstr "|- " . shows goal
showsvdash space [hyp] goal = shows hyp . strstr " |- " . shows goal
showsvdash space (hyp : hyps) goal = shows hyp . strstr ", " . showsvdash space hyps goal

showStackItem :: Set.Set LogicVar -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem fvs space (ctx, cells) = strcat
    [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- [ " . showsvdash (space + 8) hyps goal . strstr " ] # call_id = " . shows call_id | Cell facts hyps level goal call_id <- cells ] . nl
    , pindent space . strstr "+ context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " := " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
    , pindent (space + 4) . strstr "}" . nl
    ]

showsCurrentState :: Set.Set LogicVar -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState fvs ctx cells stack = strcat
    [ strstr "--------------------------------" . nl
    , strstr "* The top of the current stack is:" . nl
    , showStackItem fvs 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem fvs 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

instantiateFact :: Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr (UniqueT IO)) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_ty_pi)), [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (DC (DC_LO LO_pi)), [fact1]) -> do
            uni <- getUnique
            let var = LV_Unique uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (DC (DC_LO LO_if)), [conclusion, premise]) -> return (conclusion, premise)
        (NCon (DC (DC_LO logical_operator)), args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon LO_true)

runLogicalOperator :: LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runLogicalOperator logicalOperator args ctx facts hyps level callId cells stack
    = assertNonnegativeTerms args `seq`
      runLogicalOperatorUnchecked logicalOperator args ctx facts hyps level callId cells stack

runLogicalOperatorUnchecked :: LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runLogicalOperatorUnchecked LO_true [] ctx facts hyps level call_id cells stack
    = return ((ctx, cells) : stack)
runLogicalOperatorUnchecked LO_fail [] ctx facts hyps level call_id cells stack
    = return stack
runLogicalOperatorUnchecked LO_debug [loc_str] ctx facts hyps level call_id cells stack
    = runDebugger loc_str ctx facts hyps level call_id cells stack
runLogicalOperatorUnchecked LO_cut [] ctx facts hyps level call_id cells stack
    = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperatorUnchecked LO_and [goal1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts hyps level goal1 call_id : mkCell facts hyps level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_or [goal1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts hyps level goal1 call_id : cells) : (ctx, mkCell facts hyps level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_imply [fact1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts (fact1 : hyps) level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_sigma [goal1] ctx facts hyps level call_id cells stack
    = do
        uni <- getUnique
        let var = LV_Unique uni
        return ((ctx { _CurrentLabeling = enrollLabel var level (_CurrentLabeling ctx) }, mkCell facts hyps level (mkNApp goal1 (mkLVar var)) call_id : cells) : stack)
runLogicalOperatorUnchecked LO_pi [goal1] ctx facts hyps level call_id cells stack
    = do
        uni <- getUnique
        let con = DC (DC_Unique uni)
        return ((ctx { _CurrentLabeling = enrollLabel con (level + 1) (_CurrentLabeling ctx) }, mkCell facts hyps (level + 1) (mkNApp goal1 (mkNCon con)) call_id : cells) : stack)
runLogicalOperatorUnchecked LO_is [lhs, rhs] ctx facts hyps level call_id cells stack
    | Left "ill" == lhsValue || Left "ill" == rhsValue
    = return stack
    | LVar x <- lhs'
    , Right v <- rhsValue
    = bindIs x (NCon (DC (DC_NatL v)))
    | Right lhsValue' <- lhsValue
    , Right rhsValue' <- rhsValue
    = if lhsValue' == rhsValue'
        then return ((ctx, cells) : stack)
        else return stack
    | otherwise
    = return ((ctx { _LeftConstraints = EvalutionConstraint lhs' rhs' : _LeftConstraints ctx }, cells) : stack)
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs
        lhsValue = evaluateA lhs'
        rhsValue = evaluateA rhs'
        bindIs x rhs_s
            = execIs (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack
            where
                theta = VarBinding (Map.singleton x rhs_s)
runLogicalOperatorUnchecked logical_operator args ctx facts hyps level call_id cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

execIs :: MonadUnique m => Context -> [Cell] -> Stack -> m Stack
execIs ctx cells stack
    = assertConstraints (_LeftConstraints ctx) `seq`
      case (recheckEvaluationConstraints new_evaluation_constraints, recheckDefinedConstraints new_definition_constraints) of
        (Nothing, _) -> return stack
        (_, Nothing) -> return stack
        (Just checkedEvaluations, Just checkedDefinitions)
            | arithmeticConstraintsBad new_arithmetic_constraints -> return stack
            | otherwise -> return
                ((ctx { _LeftConstraints = map DisagreementConstraint new_disagreements
                    ++ map (uncurry EvalutionConstraint) checkedEvaluations
                    ++ map DefinedConstraint checkedDefinitions
                    ++ [ ArithmeticConstraint arith | arith <- new_arithmetic_constraints, evaluateB arith == Left "non" ] }, cells) : stack)
    where
        new_disagreements = [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ]
        new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- _LeftConstraints ctx ]
        new_definition_constraints = [ rewrite NF term | DefinedConstraint term <- _LeftConstraints ctx ]
        new_arithmetic_constraints = [ rewrite NF arith | ArithmeticConstraint arith <- _LeftConstraints ctx ]

arithmeticConstraintsBad :: [TermNode] -> Bool
arithmeticConstraintsBad terms
    = assertNonnegativeTerms terms `seq`
      List.any (\res -> evaluateB res == Right False || evaluateB res == Left "ill") terms

evaluateA :: TermNode -> Either ErrMsg Integer
evaluateA term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NCon (DC DC_Succ)) t1) = fmap succ (go t1)
    go (NApp (NApp (NCon (DC DC_plus)) t1) t2) = combine (+) (go t1) (go t2)
    go (NApp (NApp (NCon (DC DC_minus)) t1) t2) =
        case (go t1, go t2) of
            (Left "ill", _) -> Left "ill"
            (_, Left "ill") -> Left "ill"
            (Right v1, Right v2)
                | v1 >= v2 -> Right (v1 - v2)
                | otherwise -> Left "ill"
            _ -> Left "non"
    go (NApp (NApp (NCon (DC DC_mul)) t1) t2) = combine (*) (go t1) (go t2)
    go (NApp (NApp (NCon (DC DC_div)) t1) t2) =
        case (go t1, go t2) of
            (_, Right 0) -> Left "ill"
            (Left "ill", _) -> Left "ill"
            (_, Left "ill") -> Left "ill"
            (Right v1, Right v2) -> Right (v1 `div` v2)
            _ -> Left "non"
    go t = case reads (shows t "") of
        [(v, "")] -> return v
        _ -> Left "non"
    combine op lhs rhs = case (lhs, rhs) of
        (Left "ill", _) -> Left "ill"
        (_, Left "ill") -> Left "ill"
        (Right v1, Right v2) -> Right (op v1 v2)
        _ -> Left "non"

recheckEvaluationConstraints :: [(TermNode, TermNode)] -> Maybe [(TermNode, TermNode)]
recheckEvaluationConstraints = foldr step (Just []) where
    step (lhs, rhs) checked = case (evaluateA lhs', evaluateA rhs') of
        (Right lhsValue, Right rhsValue)
            | lhsValue == rhsValue -> checked
            | otherwise -> Nothing
        (Left "ill", _) -> Nothing
        (_, Left "ill") -> Nothing
        _ -> ((lhs', rhs') :) <$> checked
      where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs

-- Resolve delayed arithmetic evaluations whose right-hand side has become a
-- concrete natural.  Feed each binding back through the entire store until no
-- further directional `is' constraint can make progress.
solveEvaluationConstraints :: [(TermNode, TermNode)] -> Maybe (VarBinding, [(TermNode, TermNode)])
solveEvaluationConstraints constraints = loop mempty where
    loop theta =
        let current =
                [ (rewrite NF (bindVars theta lhs), rewrite NF (bindVars theta rhs))
                | (lhs, rhs) <- constraints
                ]
        in case firstGroundBinding current of
            Just (variable, value) ->
                let binding = VarBinding
                        (Map.singleton variable (mkNCon (DC_NatL value)))
                in loop (binding <> theta)
            Nothing -> do
                pending <- recheckEvaluationConstraints current
                return (theta, pending)

    firstGroundBinding [] = Nothing
    firstGroundBinding ((lhs, rhs) : rest) = case (rewrite NF lhs, evaluateA rhs) of
        (LVar variable, Right value) -> Just (variable, value)
        _ -> firstGroundBinding rest

recheckDefinedConstraints :: [TermNode] -> Maybe [TermNode]
recheckDefinedConstraints = foldr step (Just []) where
    step term checked = case evaluateA normalized of
        Right _ -> checked
        Left "ill" -> Nothing
        _ -> (normalized :) <$> checked
      where
        normalized = rewrite NF term

definitionUniversallyValid :: TermNode -> Bool
definitionUniversallyValid term = assertNonnegativeIndices term `seq` go (rewrite NF term) where
    go partial@(NApp (NApp (NCon (DC DC_minus)) lhs) rhs)
        | lhs == rhs = go lhs
        | otherwise = case evaluateA partial of
            Right _ -> True
            _ -> False
    go (NApp (NApp (NCon (DC DC_div)) lhs) rhs) =
        go lhs && go rhs && case evaluateA rhs of
            Right denominator -> denominator > 0
            _ -> False
    go (LVar _) = True
    go (NCon _) = True
    go (NIdx i)
        | i >= 0 = True
        | otherwise = undefined
    go (NApp lhs rhs) = go lhs && go rhs
    go (NLam body) = go body
    go suspended@Susp {} = go (rewrite NF suspended)

finalizeDefinitionConstraints :: Context -> Maybe Context
finalizeDefinitionConstraints ctx = do
    let storedBinding = _TotalVarBinding ctx
        ctx0 = ctx
            { _LeftConstraints = zonkLVar storedBinding (_LeftConstraints ctx)
            }
        evaluations =
            [ (rewrite NF lhs, rewrite NF rhs)
            | EvalutionConstraint lhs rhs <- _LeftConstraints ctx0
            ]
    (evaluationBinding, checkedEvaluations) <- solveEvaluationConstraints evaluations
    let settledCtx = zonkLVar evaluationBinding ctx0
        settledConstraints = _LeftConstraints settledCtx
        definitions =
            [ rewrite NF term
            | DefinedConstraint term <- settledConstraints
            ]
        normalizedArithmetic =
            [ rewrite NF term
            | ArithmeticConstraint term <- settledConstraints
            ]
        otherConstraints =
            [ constraint
            | constraint <- settledConstraints
            , case constraint of
                EvalutionConstraint _ _ -> False
                DefinedConstraint _ -> False
                ArithmeticConstraint _ -> False
                _ -> True
            ]
    checked <- recheckDefinedConstraints definitions
    if arithmeticConstraintsBad normalizedArithmetic
        then Nothing
        else return settledCtx
            { _LeftConstraints = otherConstraints
                ++ map (uncurry EvalutionConstraint) checkedEvaluations
                ++ map DefinedConstraint (filter (not . definitionUniversallyValid) checked)
                ++ [ ArithmeticConstraint term
                   | term <- normalizedArithmetic
                   , evaluateB term == Left "non"
                   ] }

-- ALPHA2 has no Presburger layer, so strict natural definedness is retained as
-- an explicit obligation.  Keeping it distinct from a source-level `is'
-- constraint lets the answer boundary discharge universally-total terms
-- without accidentally changing the semantics of `X is X'.
addDefinitionConstraints :: [TermNode] -> Context -> Maybe Context
addDefinitionConstraints terms ctx = do
    pending <- recheckEvaluationConstraints evaluationTerms
    pendingDefinitions <- recheckDefinedConstraints definitionTerms
    return ctx
        { _LeftConstraints = map (uncurry EvalutionConstraint) pending
            ++ map DefinedConstraint pendingDefinitions
            ++ otherConstraints }
  where
    normalized = List.nub (map (rewrite NF) terms)
    newDefinitions =
        [ DefinedConstraint term
        | term <- normalized
        , case evaluateA term of
            Right _ -> False
            _ -> True
        ]
    constraints = newDefinitions ++ _LeftConstraints ctx
    evaluationTerms =
        [ (lhs, rhs)
        | EvalutionConstraint lhs rhs <- constraints
        ]
    definitionTerms =
        [ term
        | DefinedConstraint term <- constraints
        ]
    otherConstraints =
        [ constraint
        | constraint <- constraints
        , case constraint of
            EvalutionConstraint _ _ -> False
            DefinedConstraint _ -> False
            _ -> True
        ]

strictArithmeticTerms :: Constant -> [TermNode] -> [TermNode]
strictArithmeticTerms (DC DC_eq) [typeArg, lhs, rhs]
    | NCon (TC (TC_Named "nat")) <- rewrite NF typeArg = [lhs, rhs]
strictArithmeticTerms (DC predicate) [lhs, rhs]
    | predicate `elem` [DC_le, DC_lt, DC_ge, DC_gt] = [lhs, rhs]
strictArithmeticTerms _ _ = []

evaluateB :: TermNode -> Either ErrMsg Bool
evaluateB term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NApp (NApp (NCon (DC DC_eq)) (NCon (TC (TC_Named "nat")))) t1) t2) = evaluateABinary (==) t1 t2
    go (NApp (NApp (NCon (DC DC_le)) t1) t2) = evaluateABinary (<=) t1 t2
    go (NApp (NApp (NCon (DC DC_lt)) t1) t2) = evaluateABinary (<) t1 t2
    go (NApp (NApp (NCon (DC DC_ge)) t1) t2) = evaluateABinary (>=) t1 t2
    go (NApp (NApp (NCon (DC DC_gt)) t1) t2) = evaluateABinary (>) t1 t2
    go _ = Left "non"

-- Arithmetic is strict in both operands: an unknown on one side must not
-- hide a definite partiality failure on the other side.
evaluateABinary :: (Integer -> Integer -> a) -> TermNode -> TermNode -> Either ErrMsg a
evaluateABinary op lhs rhs = case (evaluateA lhs, evaluateA rhs) of
    (Left "ill", _) -> Left "ill"
    (_, Left "ill") -> Left "ill"
    (Right lhsValue, Right rhsValue) -> Right (op lhsValue rhsValue)
    _ -> Left "non"

runDebugger :: TermNode -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runDebugger loc_str ctx facts hyps level call_id cells stack = assertNonnegativeIndices loc_str `seq` do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)

runTransition :: RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
runTransition env free_lvars stack = assertStack stack `seq` go stack where
    failure :: ExceptT KernelErr (UniqueT IO) Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr (UniqueT IO) Stack
    success with = return [with]
    arithOpCheck :: CallId -> Context -> [Cell] -> Constant -> [Fact] -> (Integer -> Integer -> Bool) -> ExceptT KernelErr (UniqueT IO) Stack
    arithOpCheck call_id ctx cells predicate args op
        = case args of
            [lhs, rhs] -> check lhs rhs
            _ -> failure
      where
        check lhs rhs = case evaluateABinary op lhs rhs of
            Left "non" -> success
                ( Context
                    { _TotalVarBinding = _TotalVarBinding ctx
                    , _CurrentLabeling = _CurrentLabeling ctx
                    , _LeftConstraints = ArithmeticConstraint (foldlNApp (NCon predicate) args) : _LeftConstraints ctx
                    , _ContextThreadId = call_id
                    , _debuggindModeOn = _debuggindModeOn ctx
                    }
                , cells
                )
            Right okay -> if okay then success (ctx, cells) else failure
            _ -> failure
    search :: Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr (UniqueT IO) Stack
    search facts hyps level predicate args ctx cells = do
        call_id <- getUnique
        let arithOpCheck' = arithOpCheck call_id ctx cells predicate args
        ans1 <- case predicate of
            DC DC_ge -> arithOpCheck' (>=)
            DC DC_gt -> arithOpCheck' (>)
            DC DC_le -> arithOpCheck' (<=)
            DC DC_lt -> arithOpCheck' (<)
            _ -> failure
        ans2 <- fmap concat $ forM (Map.findWithDefault [] predicate facts) $ \fact -> do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon predicate', args')
                    | predicate == predicate' -> do
                        hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ])) else throwE (BadFactGiven goal')
                        let new_level = level
                            new_hyps = hyps
                        case hopu_output of
                            Nothing -> failure
                            Just (new_disagreements, HopuSol new_labeling subst) -> do
                                let zonkedConstraints = zonkLVar subst (_LeftConstraints ctx)
                                    new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- zonkedConstraints ]
                                    new_definition_constraints = [ rewrite NF term | DefinedConstraint term <- zonkedConstraints ]
                                    new_arithmetic_constraints = [ rewrite NF arith | ArithmeticConstraint arith <- zonkedConstraints ]
                                case (recheckEvaluationConstraints new_evaluation_constraints, recheckDefinedConstraints new_definition_constraints) of
                                    (Nothing, _) -> failure
                                    (_, Nothing) -> failure
                                    (Just checkedEvaluations, Just checkedDefinitions)
                                        | arithmeticConstraintsBad new_arithmetic_constraints -> failure
                                        | otherwise -> success
                                        ( Context
                                            { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                                            , _CurrentLabeling = new_labeling
                                            , _LeftConstraints = map DisagreementConstraint new_disagreements
                                                ++ [ EvalutionConstraint lhs rhs | (lhs, rhs) <- checkedEvaluations ]
                                                ++ map DefinedConstraint checkedDefinitions
                                                ++ [ ArithmeticConstraint arith | arith <- new_arithmetic_constraints, evaluateB (rewrite NF arith) == Left "non" ]
                                            , _ContextThreadId = call_id
                                            , _debuggindModeOn = _debuggindModeOn ctx
                                            }
                                        , zonkLVar subst (mkCell facts new_hyps new_level new_goal call_id : cells)
                                        )
                _ -> failure
        ans3 <- fmap concat $ forM hyps $ \fact -> do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon predicate', args')
                    | predicate == predicate' -> do
                        hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ])) else throwE (BadFactGiven goal')
                        let new_level = level
                            new_hyps = hyps
                        case hopu_output of
                            Nothing -> failure
                            Just (new_disagreements, HopuSol new_labeling subst) -> do
                                let zonkedConstraints = zonkLVar subst (_LeftConstraints ctx)
                                    new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- zonkedConstraints ]
                                    new_definition_constraints = [ rewrite NF term | DefinedConstraint term <- zonkedConstraints ]
                                    new_arithmetic_constraints = [ rewrite NF arith | ArithmeticConstraint arith <- zonkedConstraints ]
                                case (recheckEvaluationConstraints new_evaluation_constraints, recheckDefinedConstraints new_definition_constraints) of
                                    (Nothing, _) -> failure
                                    (_, Nothing) -> failure
                                    (Just checkedEvaluations, Just checkedDefinitions)
                                        | arithmeticConstraintsBad new_arithmetic_constraints -> failure
                                        | otherwise -> success
                                        ( Context
                                            { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                                            , _CurrentLabeling = new_labeling
                                            , _LeftConstraints = map DisagreementConstraint new_disagreements
                                                ++ [ EvalutionConstraint lhs rhs | (lhs, rhs) <- checkedEvaluations ]
                                                ++ map DefinedConstraint checkedDefinitions
                                                ++ [ ArithmeticConstraint arith | arith <- new_arithmetic_constraints, evaluateB (rewrite NF arith) == Left "non" ]
                                            , _ContextThreadId = call_id
                                            , _debuggindModeOn = _debuggindModeOn ctx
                                            }
                                        , zonkLVar subst (mkCell facts new_hyps new_level new_goal call_id : cells)
                                        )
                _ -> failure
        return (ans1 ++ ans2 ++ ans3)
    dispatch :: Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
    dispatch ctx facts hyps level (NCon predicate, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts hyps level call_id cells stack
            go stack'
        | otherwise
        = case addDefinitionConstraints (strictArithmeticTerms predicate args) ctx of
            Nothing -> go stack
            Just strictCtx -> do
                stack' <- search facts hyps level predicate args strictCtx cells
                go (stack' ++ stack)
    dispatch ctx facts hyps level (t, ts) call_id cells stack = throwE (BadGoalGiven (foldlNApp t ts))
    go :: Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
    go [] = return False
    go ((ctx, cells) : stack) = do
        liftIO $ do
            dbg <- readIORef (_debuggindModeOn ctx)
            when dbg $ _PutStr env ctx (showsCurrentState free_lvars ctx cells stack "")
        case cells of
            [] -> case finalizeDefinitionConstraints ctx of
                Nothing -> go stack
                Just answerContext -> do
                    want_more <- liftIO (_Answer env answerContext)
                    if want_more then go stack else return True
            Cell facts hyps level goal call_id : cells -> dispatch ctx facts hyps level (unfoldlNApp (rewrite HNF goal)) call_id cells stack

eraseTrivialBinding :: LogicVarSubst -> LogicVarSubst
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
        | not (hasName v1) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v1 (LVar v2) })) . Map.delete v1
        | otherwise = id
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t
        = case viewNestedNLam (rewrite NF t) of
            (n, t') -> case unfoldlNApp t' of
                (LVar v, ts) -> if ts == map mkNIdx [n - 1, n - 2 .. 0] then Just v else Nothing
                _ -> Nothing
