module Jasmine.Alpha1.Solver.HOPU.Internal where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Jasmine.Alpha1.Solver.HOPU.Util
import Z.Algo.Function
import Z.Utils

infix 2 <==

simplify :: GeneratingUniqueMonad m => [Problem] -> StateT AtomEnv m [Problem]
simplify [] = return []
simplify ((lhs :==: rhs) : probs) = do
    env <- get
    new_probs <- simplifyUnificationProblemOnce (flatten env lhs) (flatten env rhs)
    simplify (new_probs ++ probs)
simplify (prob : probs) = do
    new_probs <- simplify probs
    return (prob : new_probs)

simplifyUnificationProblemOnce :: GeneratingUniqueMonad m => TermNode -> TermNode -> StateT AtomEnv m [Problem]
simplifyUnificationProblemOnce lhs rhs
    | (l1, t1) <- viewNLam lhs
    , (l2, t2) <- viewNLam rhs
    , l1 > 0 && l2 > 0
    = case l1 `compare` l2 of
        LT -> simplifyUnificationProblemOnce t1 (unviewNLam (l2 - l1) t2)
        EQ -> simplifyUnificationProblemOnce t1 t2
        GT -> simplifyUnificationProblemOnce (unviewNLam (l1 - l2) t1) t2
    | (t1, ts1) <- viewNApp lhs
    , (l2, t2) <- viewNLam rhs
    , l2 > 0
    = simplifyUnificationProblemOnce (unviewNApp (liftLam l2 t1) (map (liftLam l2) ts1 ++ map mkNIdx [l2 - 1, l2 - 2 .. 0])) t2
    | (l1, t1) <- viewNLam lhs
    , (t2, ts2) <- viewNApp rhs
    , l1 > 0
    = simplifyUnificationProblemOnce t1 (unviewNApp (liftLam l1 t2) (map (liftLam l1) ts2 ++ map mkNIdx [l1 - 1, l1 - 2 .. 0]))
    | otherwise
    = simplifyUnificationProblemNApp (viewNApp lhs) (viewNApp rhs)

simplifyUnificationProblemNApp :: GeneratingUniqueMonad m => (TermNode, [TermNode]) -> (TermNode, [TermNode]) -> StateT AtomEnv m [Problem]
simplifyUnificationProblemNApp (t1, ts1) (t2, ts2)
    | t1 == fromPrim TmWcard = return []
    | t2 == fromPrim TmWcard = return []
    | t1 == fromPrim SPY = return [Delayed BySpy (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t2 == fromPrim SPY = return [Delayed BySpy (unviewNApp t2 ts2) (unviewNApp t1 ts1)]
    | isRigid t1 && isRigid t2
    = if t1 == t2 && length ts1 == length ts2
        then simplify (zipWith (:==:) ts1 ts2)
        else return [Delayed ByRew (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t1 == fromPrim TmGuard = return [Delayed GUARD (unviewNApp t1 ts1) (unviewNApp t2 ts2)]
    | t2 == fromPrim TmGuard = return [Delayed GUARD (unviewNApp t2 ts2) (unviewNApp t1 ts1)]
    | Just x <- getLVar t1 = makeSubstitution (x, ts1) (unviewNApp t2 ts2)
    | Just x <- getLVar t2 = makeSubstitution (x, ts2) (unviewNApp t1 ts1)
    | otherwise = return [Delayed ByERR (unviewNApp t1 ts1) (unviewNApp t2 ts2)]

makeSubstitution :: GeneratingUniqueMonad m => (Unique, [TermNode]) -> TermNode -> StateT AtomEnv m [Problem]
makeSubstitution (fun, args) rhs
    | null args
    = makeSubstitutionFirstOrder fun rhs
    | (l, t2) <- viewNLam rhs
    , l > 0
    = makeSubstitution (fun, map (liftLam l) args ++ map mkNIdx [l - 1, l - 2 .. 0]) t2
    | (fun', params) <- viewNApp rhs
    , mkLVar fun == fun'
    = do
        env <- get
        let var = logicvar fun
        if runReader (isPatternWRT args var) env
            then do
                t <- getNewAtom (getScopeLevel env var)
                let n = length args - 1
                    body = unviewNApp t [ mkNIdx (n - i) | i <- [0, 1 .. n], args !! i == params !! i ]
                makeSubstitutionFirstOrder fun (unviewNLam (length args) body)
            else return [Delayed ByNaP (unviewNApp (mkLVar fun) args) rhs]
    | otherwise
    = do
        env <- get
        if runReader (isPatternWRT args (logicvar fun)) env
            then do
                env <- get
                res <- lift (runExceptT (runStateT ((fun, args) <== rhs) env))
                case res of
                    Left err_cause -> return [Delayed err_cause (unviewNApp (mkLVar fun) args) rhs]
                    Right ((body, new_probs), env') -> do
                        put env'
                        probs <- makeSubstitutionFirstOrder fun (unviewNLam (length args) body)
                        return (new_probs ++ probs)
            else return [Delayed ByNaP (unviewNApp (mkLVar fun) args) rhs]

makeSubstitutionFirstOrder :: GeneratingUniqueMonad m => Unique -> TermNode -> StateT AtomEnv m [Problem]
makeSubstitutionFirstOrder var rhs
    | mkLVar var == rhs = return []
    | var `Set.member` collectUniqs rhs = return [Delayed OCCUR (mkLVar var) rhs]
    | otherwise = do
        env <- get
        put (Map.alter (Just . maybe (AtomInfo { _scope_lv = getNewScope env maxBound, _eval_ref = Just rhs, _type_ref = Nothing }) (\info -> info { _scope_lv = getNewScope env (_scope_lv info) })) var env)
        case Map.lookup var env of
            Nothing -> return []
            Just info -> simplify (maybe [] (\lhs -> [lhs :==: rhs]) (_eval_ref info))
    where
        getNewScope :: AtomEnv -> ScopeLevel -> ScopeLevel
        getNewScope env old_one = callWithStrictArg (maybe old_one id . Set.lookupMin) (Set.map (maybe maxBound _scope_lv . flip Map.lookup env) (collectUniqs rhs))

(<==) :: GeneratingUniqueMonad m => (Unique, [TermNode]) -> TermNode -> StateT AtomEnv (ExceptT Cause m) (TermNode, [Problem])
(<==) = uncurry (go 0) where
    dispatch :: GeneratingUniqueMonad m => SmallNat -> Unique -> [TermNode] -> TermNode -> StateT AtomEnv (ExceptT Cause m) (TermNode, [Problem])
    dispatch l fun args rhs
        | (l', rhs') <- viewNLam rhs
        , l' > 0
        = do
            (body, probs) <- go (l + l') fun args rhs'
            return (unviewNLam l' body, probs)
        | (t', ts') <- viewNApp rhs
        , isRigid t'
        = do
            env <- get
            t <- getNewHead env (logicvar fun) t' ([ rewriteWithSusp arg 0 l [] NF | arg <- args ] ++ map mkNIdx [l - 1, l - 2 .. 0])
            (ts, probs) <- getNewTail l fun args ts'
            return (unviewNApp t ts, probs)
        | (t', args') <- viewNApp rhs
        , Just fun' <- getLVar t'
        = if fun == fun'
            then lift (throwE OCCUR)
            else do
                env <- get
                if runReader (isPatternWRT args' (logicvar fun')) env
                    then flexflex env (fun, map (liftLam l) args ++ map mkNIdx [l - 1, l - 2 .. 0]) (fun', args')
                    else lift (throwE ByNaP)
        | otherwise
        = lift (throwE ByERR)
    getNewHead :: GeneratingUniqueMonad m => AtomEnv -> AtomNode -> TermNode -> [TermNode] -> StateT AtomEnv (ExceptT Cause m) TermNode
    getNewHead env v t params
        | Atom c <- t
        , getScopeLevel env v >= getScopeLevel env c
        = return t
        | Just i <- t `List.elemIndex` params
        = return (mkNIdx (length params - 1 - i))
        | otherwise
        = lift (throwE NotFR)
    getNewTail :: GeneratingUniqueMonad m => SmallNat -> Unique -> [TermNode] -> [TermNode] -> StateT AtomEnv (ExceptT Cause m) ([TermNode], [Problem])
    getNewTail l fun args [] = return ([], [])
    getNewTail l fun args (t : ts) = do
        (t', probs) <- go l fun args t
        (ts', new_probs) <- getNewTail l fun args ts
        return (t' : ts', probs ++ new_probs)
    flexflex :: GeneratingUniqueMonad m => AtomEnv -> (Unique, [TermNode]) -> (Unique, [TermNode]) -> StateT AtomEnv (ExceptT Cause m) (TermNode, [Problem])
    flexflex env (fun, args) (fun', args') = do
        let var = logicvar fun
            var' = logicvar fun'
            scope_compare = getScopeLevel env var `compare` getScopeLevel env var'
            common_args = Set.toList (Set.fromList args `Set.intersection` Set.fromList args')
            selecteds = fromJust (if scope_compare == LT then runReaderT (args `up` var') env else runReaderT (args' `up` var) env)
        (lhs_inner, rhs_inner) <- case scope_compare of
            LT -> return (fromJust (selecteds `down` args), selecteds)
            ge -> return (selecteds, fromJust (selecteds `down` args'))
        let lhs_outer = fromJust (common_args `down` args)
            rhs_outer = fromJust (common_args `down` args')
        t <- getNewAtom (getScopeLevel env var)
        probs <- makeSubstitutionFirstOrder fun' (unviewNLam (length args') (unviewNApp t (rhs_inner ++ rhs_outer)))
        return (unviewNApp t (lhs_inner ++ lhs_outer), probs)
    go :: GeneratingUniqueMonad m => SmallNat -> Unique -> [TermNode] -> TermNode -> StateT AtomEnv (ExceptT Cause m) (TermNode, [Problem])
    go l fun args rhs = do
        env <- get
        dispatch l fun (map (flatten env) args) (flatten env rhs)

getNewAtom :: GeneratingUniqueMonad m => ScopeLevel -> StateT AtomEnv m TermNode
getNewAtom lv = do
    h <- getNewUnique
    modify (Map.insert h (AtomInfo { _scope_lv = lv, _eval_ref = Nothing, _type_ref = Nothing }))
    return (mkLVar h)
