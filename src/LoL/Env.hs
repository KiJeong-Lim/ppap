module LoL.Env (Decl (..), Entry (..), Env, Refusal (..), Mode (..), emptyEnv, envDecls, envNames, envFresh, declType, declBody, reducibleBody, declTerms, reachable, factsFor, allFacts, assumptions, admissionGoal, declare, declareIn, typeOfTerm, normalForm, askIn) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.TermNode (LogicVar (..), TermNode)
import LoL.Core
import LoL.Hol.Embed
import LoL.Hol.Session

-- `Definition a t` and `Theorem a t` have type `a` and body `t`.
data Decl
    = Axiom Term
    | Definition Term Term
    | Theorem Term Term
    deriving (Eq, Show)

data Entry
    = Entry
        { entryName :: String
        , entryDecl :: Decl
        }
    deriving (Eq, Show)

-- The declarations, their names, the next constant, and the stamp of this
-- environment. Only `declare` makes an environment with declarations, and it
-- gives each one a stamp of its own: two environments with the same stamp have
-- the same declarations.
data Env
    = Env (Map.Map ConstId Entry) (Map.Map String ConstId) ConstId (Maybe Stamp)
    deriving (Show)

instance Eq Env where
    Env decls1 names1 fresh1 _ == Env decls2 names2 fresh2 _ = decls1 == decls2 && names1 == names2 && fresh1 == fresh2

envDecls :: Env -> Map.Map ConstId Entry
envDecls (Env decls _ _ _) = decls

envNames :: Env -> Map.Map String ConstId
envNames (Env _ names _ _) = names

envFresh :: Env -> ConstId
envFresh (Env _ _ fresh _) = fresh

envStamp :: Env -> Maybe Stamp
envStamp (Env _ _ _ stamp) = stamp

-- How a ground run gets the facts of its environment. `Persistent`: from the
-- engine that the kernel keeps, which holds every fact of the environment.
-- `Reference`: a machine of its own with the facts of the declarations that the
-- run depends on (doc/LoLALPHA1.txt, 5.2). The two give the same verdict.
data Mode
    = Persistent
    | Reference
    deriving (Eq, Show)

data Refusal
    = DuplicateName String
    | NotClosed
    | KernelRejected (Maybe Report)
    | KernelUndecided String
    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty 0 Nothing

declType :: Decl -> Term
declType decl
    = case decl of
        Axiom a -> a
        Definition a _ -> a
        Theorem a _ -> a

declBody :: Decl -> Maybe Term
declBody decl
    = case decl of
        Axiom _ -> Nothing
        Definition _ t -> Just t
        Theorem _ t -> Just t

-- Only a `Definition` reduces (LoLCore [R-Delta]): the kernel never sees the body of a `Theorem`.
reducibleBody :: Decl -> Maybe Term
reducibleBody decl
    = case decl of
        Definition _ t -> Just t
        _ -> Nothing

declTerms :: Decl -> [Term]
declTerms decl = declType decl : maybe [] pure (declBody decl)

-- The constants a run can reach from `roots`: through types, and through the bodies that reduce.
reachable :: (Decl -> Maybe Term) -> Env -> Set.Set ConstId -> Set.Set ConstId
reachable bodyOf env roots = go Set.empty (Set.toList roots) where
    go seen [] = seen
    go seen (c : rest)
        | Set.member c seen = go seen rest
        | otherwise = case Map.lookup c (envDecls env) of
            Nothing -> go seen rest
            Just entry -> go (Set.insert c seen) (Set.toList (mentioned (entryDecl entry)) ++ rest)
    mentioned decl = Set.unions (map constantsOf (declType decl : maybe [] pure (bodyOf decl)))

-- The facts of doc/LoLALPHA1.txt, 5.2, for one declaration.
declFacts :: ConstId -> Decl -> [TermNode]
declFacts c decl = cstTypeFact c (declType decl) : maybe [] (pure . cstBodyFact c) (reducibleBody decl)

-- The facts of the declarations that `terms` depend on.
factsFor :: Env -> [Term] -> [TermNode]
factsFor env terms = concatMap facts (Set.toAscList (reachable reducibleBody env (Set.unions (map constantsOf terms)))) where
    facts c = maybe [] (declFacts c . entryDecl) (Map.lookup c (envDecls env))

-- The facts of every declaration.
allFacts :: Env -> [TermNode]
allFacts env = concat [declFacts c (entryDecl entry) | (c, entry) <- Map.toAscList (envDecls env)]

run :: Mode -> Kernel -> Limits -> Env -> [Term] -> TermNode -> [LogicVar] -> IO Verdict
run mode kernel limits env terms goal outputs
    = case mode of
        Persistent -> loadedRun kernel limits (envStamp env) (allFacts env) goal outputs
        Reference -> groundRun kernel limits (factsFor env terms) goal outputs

-- Assumptions(c) of LoLCore, Chapter 8: the bodies of theorems count.
assumptions :: Env -> ConstId -> Set.Set ConstId
assumptions env c = Set.filter isAxiom (reachable declBody env (Set.singleton c)) where
    isAxiom d = case Map.lookup d (envDecls env) of
        Just (Entry { entryDecl = Axiom _ }) -> True
        _ -> False

admissionGoal :: Decl -> TermNode
admissionGoal decl
    = case decl of
        Axiom a -> admitAxGoal a
        Definition a t -> admitDefGoal a t
        Theorem a t -> admitDefGoal a t

declare :: Kernel -> Limits -> Env -> String -> Decl -> IO (Either Refusal (ConstId, Env))
declare = declareIn Persistent

-- B1: the environment grows only after a ground run of the kernel has admitted the declaration.
declareIn :: Mode -> Kernel -> Limits -> Env -> String -> Decl -> IO (Either Refusal (ConstId, Env))
declareIn mode kernel limits env name decl
    | Map.member name (envNames env) = return (Left (DuplicateName name))
    | not (all (wellScoped 0) (declTerms decl)) = return (Left NotClosed)
    | otherwise = do
        verdict <- run mode kernel limits env (declTerms decl) (admissionGoal decl) []
        case verdict of
            Admitted _ -> do
                stamp <- newStamp
                loadedExtend kernel (envStamp env) stamp (declFacts c decl)
                return (Right (c, Env (Map.insert c (Entry { entryName = name, entryDecl = decl }) (envDecls env)) (Map.insert name c (envNames env)) (c + 1) (Just stamp)))
            Rejected report -> return (Left (KernelRejected report))
            Undecided reason -> return (Left (KernelUndecided reason))
    where
        c = envFresh env

typeOfTerm :: Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
typeOfTerm = askIn Persistent typeGoal

normalForm :: Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
normalForm = askIn Persistent normalGoal

askIn :: Mode -> (Term -> LogicVar -> TermNode) -> Kernel -> Limits -> Env -> Term -> IO (Either Refusal Term)
askIn mode goalOf kernel limits env term
    | not (wellScoped 0 term) = return (Left NotClosed)
    | otherwise = do
        verdict <- run mode kernel limits env [term] (goalOf term output) [output]
        return $ case verdict of
            Admitted [answer] -> Right answer
            Admitted _ -> Left (KernelUndecided "the run did not return one output")
            Rejected report -> Left (KernelRejected report)
            Undecided reason -> Left (KernelUndecided reason)
    where
        output = LV_Named "Out"
