module Main where

import Control.Monad
import Data.List (elemIndex)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.TermNode (LogicVar (..), TermNode, foldlNApp, mkLVar, mkNApp)
import LoL.Core
import LoL.Env
import LoL.Hol.Embed
import LoL.Hol.Session

expect :: String -> Bool -> IO ()
expect name okay = unless okay (ioError (userError name))

-- Terms with names, for writing the tests. Resolving names is the only thing done to them.
data Raw
    = RProp
    | RType Integer
    | RName String
    | RPi String Raw Raw
    | RArr Raw Raw
    | RLam String Raw Raw
    | RLet String Raw Raw Raw
    | RApp Raw [Raw]
    deriving ()

resolve :: Env -> [String] -> Raw -> Term
resolve env locals raw
    = case raw of
        RProp -> Prop
        RType l -> Type l
        RName x -> maybe (Cst (Map.findWithDefault 999 x (envNames env))) Var (elemIndex x locals)
        RPi x a b -> Pi x (resolve env locals a) (resolve env (x : locals) b)
        RArr a b -> Pi "" (resolve env locals a) (resolve env ("" : locals) b)
        RLam x a t -> Lam x (resolve env locals a) (resolve env (x : locals) t)
        RLet x t a u -> Let x (resolve env locals t) (resolve env locals a) (resolve env (x : locals) u)
        RApp f args -> apps (resolve env locals f) (map (resolve env locals) args)

closed :: Env -> Raw -> Term
closed env = resolve env []

step :: Int -> Int
step seed = (seed * 1103515245 + 12345) `mod` 2147483648

-- A well-scoped term from a seed: the property tests need many shapes, not a distribution.
generate :: Int -> Int -> Int -> (Term, Int)
generate fuel scope seed
    | fuel <= 0 = leaf
    | otherwise = case seed `mod` 8 of
        0 -> binary (Pi "x") 1
        1 -> binary (Lam "y") 1
        2 -> binary App 0
        3 -> binary App 0
        4 -> ternary
        _ -> leaf
    where
        leaf = case (seed `div` 8) `mod` 4 of
            0 -> (Prop, step seed)
            1 -> (Type (toInteger ((seed `div` 32) `mod` 4)), step seed)
            2 -> (Cst (toInteger ((seed `div` 32) `mod` 6)), step seed)
            _ -> (if scope > 0 then Var ((seed `div` 32) `mod` scope) else Prop, step seed)
        binary make extra = (make left right, seed2) where
            (left, seed1) = generate (fuel - 1) scope (step seed)
            (right, seed2) = generate (fuel - 1) (scope + extra) seed1
        ternary = (Let "z" one two three, seed3) where
            (one, seed1) = generate (fuel - 1) scope (step seed)
            (two, seed2) = generate (fuel - 1) scope seed1
            (three, seed3) = generate (fuel - 1) (scope + 1) seed2

samples :: Int -> [Term]
samples count = take count (go 20261111) where
    go seed = term : go next where
        (term, next) = generate 6 0 seed

rejectedBy :: String -> Either Refusal a -> Bool
rejectedBy rule outcome
    = case outcome of
        Left (KernelRejected (Just report)) -> reportRule report == rule
        _ -> False

undecided :: Either Refusal a -> Bool
undecided outcome
    = case outcome of
        Left (KernelUndecided _) -> True
        _ -> False

declareAll :: Kernel -> Env -> [(String, Env -> Decl)] -> IO Env
declareAll kernel = foldM add where
    add env (name, make) = do
        outcome <- declare kernel defaultLimits env name (make env)
        case outcome of
            Right (_, extended) -> return extended
            Left refusal -> ioError (userError ("declaration " ++ name ++ " was refused: " ++ show refusal))

church :: [(String, Env -> Decl)]
church =
    [ ("cnat", \env -> Definition (Type 1) (closed env (RPi "a" (RType 0) (RArr (RArr a a) (RArr a a)))))
    , ("zero", \env -> Definition (closed env cnat) (closed env (numeral x)))
    , ("succ", \env -> Definition (closed env (RArr cnat cnat)) (closed env (RLam "n" cnat (numeral (RApp f [RApp n [a, f, x]])))))
    , ("add", \env -> Definition (closed env (RArr cnat (RArr cnat cnat))) (closed env (RLam "m" cnat (RLam "n" cnat (numeral (RApp m [a, f, RApp n [a, f, x]]))))))
    , ("mul", \env -> Definition (closed env (RArr cnat (RArr cnat cnat))) (closed env (RLam "m" cnat (RLam "n" cnat (RLam "a" (RType 0) (RLam "f" (RArr a a) (RApp m [a, RApp n [a, f]])))))))
    , ("two", \env -> Definition (closed env cnat) (closed env (RApp succ' [RApp succ' [zero]])))
    , ("four", \env -> Definition (closed env cnat) (closed env (RApp succ' [RApp succ' [RApp succ' [RApp succ' [zero]]]])))
    ]
    where
        [a, f, x, m, n, cnat, zero, succ'] = map RName ["a", "f", "x", "m", "n", "cnat", "zero", "succ"]

numeral :: Raw -> Raw
numeral body = RLam "a" (RType 0) (RLam "f" (RArr (RName "a") (RName "a")) (RLam "x" (RName "a") body))

-- The Church numeral of `count`, written out.
literal :: Int -> Raw
literal count = numeral (iterate (\body -> RApp (RName "f") [body]) (RName "x") !! count)

-- `forall q : cnat -> Prop, q left -> q right`, proved by the identity: admitted exactly when left == right.
sameNumeral :: Env -> String -> String -> Decl
sameNumeral env left right = sameTerm env (RName left) (RName right)

sameTerm :: Env -> Raw -> Raw -> Decl
sameTerm env left right = Theorem (closed env statement) (closed env proof) where
    predicate = RArr (RName "cnat") RProp
    statement = RPi "q" predicate (RArr (RApp (RName "q") [left]) (RApp (RName "q") [right]))
    proof = RLam "q" predicate (RLam "h" (RApp (RName "q") [left]) (RName "h"))

main :: IO ()
main = do
    loaded <- loadKernel "lol/hol/kernel.hol"
    kernel <- either (ioError . userError) return loaded
    let limits = defaultLimits
        goal name args = foldlNApp (named name) args
        x = LV_Named "X"
        y = LV_Named "Y"
        identityType = closed emptyEnv (RPi "a" (RType 0) (RArr (RName "a") (RName "a")))
        identity = closed emptyEnv (RLam "a" (RType 0) (RLam "x" (RName "a") (RName "x")))

    forM_ (samples 2000) $ \term ->
        expect ("a term changed between Core and Hol: " ++ show term) (wellScoped 0 term && recoverTerm (embedTerm term) == Right term)
    expect "binder names do not take part in equality" (Lam "x" Prop (Var 0) == Lam "another" Prop (Var 0) && Lam "x" Prop (Var 0) /= Lam "x" Prop Prop)
    expect "a binder name that Hol cannot display is dropped" (recoverTerm (embedTerm (Lam "Upper" Prop (Lam "pi" Prop (Lam "" Prop (Var 2))))) == Right (Lam "" Prop (Lam "" Prop (Lam "" Prop (Var 2)))))
    expect "a term of another signature is not a Core term" (either (const True) (const False) (recoverTerm (named "rep")))

    forM_ (take 40 (samples 2000)) $ \term -> do
        verdict <- groundRun kernel limits [] (goal "conv" [mkLVar x, embedTerm term]) [x]
        expect ("a term changed on its way through the engine: " ++ show term) (verdict == Admitted [term])

    admitted <- declare kernel limits emptyEnv "identity" (Definition identityType identity)
    expect "the identity is admitted and numbered" (fmap fst admitted == Right 0)
    typeInType <- declare kernel limits emptyEnv "bad" (Definition (Type 0) (Type 0))
    expect "Type@{0} : Type@{0} is rejected by [T-Conv]" (rejectedBy "T-Conv" typeInType)
    notAType <- declare kernel limits emptyEnv "bad" (Axiom identity)
    expect "an axiom that is not a type is rejected by [D-Ax]" (rejectedBy "D-Ax" notAType)
    unknown <- declare kernel limits emptyEnv "bad" (Definition Prop (Cst 7))
    expect "an undeclared constant is rejected by [T-Const]" (rejectedBy "T-Const" unknown)
    local <- declare kernel limits emptyEnv "local" (Definition (Type 1) (closed emptyEnv (RLet "a" RProp (RType 1) (RPi "p" (RName "a") (RName "p")))))
    expect "a let is given to the kernel as definition, type, body" (either (const False) (const True) local)
    swapped <- declare kernel limits emptyEnv "bad" (Definition (Type 1) (closed emptyEnv (RLet "a" (RType 1) RProp (RPi "p" (RName "a") (RName "p")))))
    expect "a let whose definition and type are exchanged is rejected by [T-Conv]" (rejectedBy "T-Conv" swapped)
    open <- declare kernel limits emptyEnv "bad" (Axiom (Var 0))
    expect "an open declaration never reaches the kernel" (open == Left NotClosed)
    expect "a refused declaration leaves the environment unchanged" (either (const True) (const False) typeInType)

    env <- declareAll kernel emptyEnv church
    duplicate <- declare kernel limits env "two" (Axiom Prop)
    expect "a declared name cannot be declared again" (duplicate == Left (DuplicateName "two"))
    typeOfTwo <- typeOfTerm kernel limits env (closed env (RName "two"))
    expect "the type of a constant is its declared type" (typeOfTwo == Right (closed env (RName "cnat")))
    sum <- normalForm kernel limits env (closed env (RApp (RName "add") [RName "two", RName "two"]))
    four <- normalForm kernel limits env (closed env (RName "four"))
    expect "2 + 2 and 4 have the same normal form" (sum == four && either (const False) (const True) four)
    expect "the normal form of 4 is the numeral" (four == Right (closed env (RLam "a" (RType 0) (RLam "f" (RArr (RName "a") (RName "a")) (RLam "x" (RName "a") (RApp (RName "f") [RApp (RName "f") [RApp (RName "f") [RApp (RName "f") [RName "x"]]]]))))))

    let twoBody = closed env (RApp (RName "succ") [RApp (RName "succ") [RName "zero"]])
        cnat = closed env (RName "cnat")
    opaque <- declareAll kernel env [("opaque", const (Theorem cnat twoBody)), ("clear", const (Definition cnat twoBody))]
    viaTheorem <- declare kernel limits opaque "t1" (sameNumeral opaque "opaque" "two")
    viaDefinition <- declare kernel limits opaque "t2" (sameNumeral opaque "clear" "two")
    expect "a theorem does not reduce to its body" (rejectedBy "T-Conv" viaTheorem)
    expect "a definition reduces to its body" (either (const False) (const True) viaDefinition)
    expect "the facts of a definition follow its body" (length (factsFor opaque [closed opaque (RName "two")]) == 8)

    large <- declareAll kernel env
        [ ("n128", \e -> Definition (closed e (RName "cnat")) (closed e (literal 128)))
        , ("n16384", \e -> Definition (closed e (RName "cnat")) (closed e (literal 16384)))
        ]
    let square = RApp (RName "mul") [RName "n128", RName "n128"]
    product <- normalForm kernel limits large (closed large square)
    expect "the normal form of 128 * 128 is the numeral of 16384" (product == Right (closed large (literal 16384)))
    converted <- declare kernel limits large "square" (sameTerm large square (RName "n16384"))
    expect ("128 * 128 converts with 16384: " ++ show (fmap fst converted)) (either (const False) (const True) converted)
    different <- declare kernel limits large "bad" (sameTerm large square (RName "n128"))
    expect "128 * 128 does not convert with 128" (rejectedBy "T-Conv" different)
    expect "the facts of a theorem stop at its type" (length (factsFor opaque [closed opaque (RName "opaque")]) == 3)

    assumed <- declareAll kernel env
        [ ("ax", \e -> Axiom (closed e (RName "cnat")))
        , ("thm", \e -> Theorem (closed e (RName "cnat")) (closed e (RApp (RName "succ") [RName "ax"])))
        , ("def", \e -> Definition (closed e (RName "cnat")) (closed e (RApp (RName "succ") [RName "thm"])))
        ]
    let numberOf name = Map.findWithDefault (-1) name (envNames assumed)
    expect "assumptions are found through the body of a theorem" (assumptions assumed (numberOf "def") == Set.singleton (numberOf "ax"))
    expect "a constant without axioms has no assumption" (Set.null (assumptions assumed (numberOf "four")))

    notGround <- groundRun kernel limits [] (goal "admit_ax" [mkNApp (named "typ") (mkLVar x)]) []
    expect "R1: a query with a logic variable is not run" (notGround == Undecided "the query has a logic variable that is not an output")
    unbound <- runGoal kernel limits [] (goal "conv" [mkLVar x, mkLVar y]) [x]
    expect "R3: an answer with a logic variable does not admit" (unbound == Undecided "the answer has a logic variable")
    answered <- runGoal kernel limits [] (goal "admit_ax" [mkNApp (named "typ") (mkLVar x)]) []
    expect "the engine does answer the query that R1 refuses" (answered == Admitted [])
    residual <- runGoal kernel limits [] (goal "conv" [mkNApp (mkLVar x) (named "prop"), named "prop"]) []
    expect ("R3: an answer with a residual constraint does not admit: " ++ show residual) (residual == Undecided "the answer has a residual constraint")

    let omega = App half half
        half = Lam "x" Prop (App (Var 0) (Var 0))
    looping <- normalForm kernel (limits { limitMicros = 2000000 }) emptyEnv omega
    expect ("R5: a run that reaches the time limit is undecided: " ++ show looping) (looping == Left (KernelUndecided "the time limit was reached"))
    starved <- normalForm kernel (limits { limitVisits = Just 1 }) env (closed env (RName "four"))
    expect ("R5: a run that reaches the work limit is undecided: " ++ show starved) (undecided starved)
    after <- normalForm kernel limits env (closed env (RName "four"))
    expect "the kernel is usable after an undecided run" (after == four)

    -- The engine that the kernel keeps holds the facts of one environment. The
    -- three branches of `env` give constant 7 to a theorem, a numeral and an axiom.
    expect "the branches number their first constant alike" (map (fmap entryName . Map.lookup 7 . envDecls) [opaque, large, assumed] == map Just ["opaque", "n128", "ax"])
    forM_ [assumed, large, opaque, large, assumed, env, emptyEnv, opaque] $ \branch -> do
        forM_ [Cst 7, App (Cst 2) (Cst 7), closed env (RApp (RName "add") [RName "two", RName "two"])] $ \term -> do
            kept <- mapM (\goal -> askIn Persistent goal kernel limits branch term) [typeGoal, normalGoal]
            fresh <- mapM (\goal -> askIn Reference goal kernel limits branch term) [typeGoal, normalGoal]
            expect ("the kept engine and a fresh machine disagree on " ++ show term) (kept == fresh)
        seventh <- normalForm kernel limits branch (Cst 7)
        typed <- typeOfTerm kernel limits branch (Cst 7)
        expect ("a constant reduces as its own environment declares it: " ++ show seventh) (seventh == Right (if fmap entryName (Map.lookup 7 (envDecls branch)) == Just "n128" then closed large (literal 128) else Cst 7))
        expect ("a constant has a type exactly where it is declared: " ++ show typed) (if Map.member 7 (envDecls branch) then typed == Right (closed env (RName "cnat")) else rejectedBy "T-Const" typed)
    replayed <- foldM (\known (name, make) -> declareIn Reference kernel limits known name (make known) >>= either (ioError . userError . show) (return . snd)) emptyEnv church
    expect "fresh machines admit the same declarations" (replayed == env)
    let eight = Definition (closed env (RName "cnat")) (closed env (RApp (RName "add") [RName "four", RName "four"]))
    forM_ [("bad", Definition (Type 0) (Type 0)), ("bad", Axiom identity), ("bad", Definition Prop (Cst 7)), ("two", Axiom Prop), ("eight", eight)] $ \(name, decl) -> do
        kept <- declareIn Persistent kernel limits env name decl
        fresh <- declareIn Reference kernel limits env name decl
        expect ("the kept engine and a fresh machine disagree on the declaration " ++ name) (kept == fresh)
    let link known index = Definition (closed env (RName "cnat")) (if index == 0 then closed env (RName "four") else Cst (envFresh known - 1))
    long <- foldM (\known index -> declare kernel limits known ("link" ++ show index) (link known index) >>= either (ioError . userError . show) (return . snd)) env [0 :: Int .. 299]
    end <- normalForm kernel limits long (Cst (envFresh long - 1))
    expect "a chain of 300 definitions unfolds to its first link" (end == four && Map.size (envDecls long) == 307)
    older <- typeOfTerm kernel limits env (Cst (envFresh long - 1))
    again <- normalForm kernel limits long (Cst (envFresh long - 1))
    expect "an older environment does not see what was declared after it" (rejectedBy "T-Const" older && again == four)

    putStrLn "LoL host: Core and Hol terms round-trip, declarations go through ground runs, and R1, R3, R5 hold"
    putStrLn "LoL host: the kept engine agrees with fresh machines across branching environments"
