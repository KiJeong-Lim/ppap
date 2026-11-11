module LoL.Hol.Embed where

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Debugger (initialCache, prettyTerm)
import Hol.BETA.Header (DataConstructor (..), SmallId, reservedNamedIdentifiers)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.TermNode
import LoL.Core

-- The constants of this module are those of `lol/hol/kernel.hol` (doc/LoLALPHA1.txt, 5.1 to 5.5).

data Report
    = Report
        { reportRule :: String
        , reportArgs :: [String]
        }
    deriving (Eq, Show)

named :: SmallId -> TermNode
named = mkNCon . DC_Named

natural :: Integer -> TermNode
natural = mkNCon . DC_NatL

embedLevel :: Level -> TermNode
embedLevel level
    | level <= 0 = named "lz"
    | otherwise = mkNApp (named "ls") (embedLevel (level - 1))

-- A Core binder is one Hol abstraction, so the de Bruijn indices coincide.
embedTerm :: Term -> TermNode
embedTerm term
    = case term of
        Prop -> named "prop"
        Type l -> mkNApp (named "typ") (embedLevel l)
        Cst c -> mkNApp (named "cst") (natural c)
        Var i -> mkNIdx i
        Pi x a b -> foldlNApp (named "prod") [embedTerm a, embedBinder x b]
        Lam x a t -> foldlNApp (named "lam") [embedTerm a, embedBinder x t]
        Let x t a u -> foldlNApp (named "letin") [embedTerm t, embedTerm a, embedBinder x u]
        App t u -> foldlNApp (named "app") [embedTerm t, embedTerm u]

embedBinder :: Hint -> Term -> TermNode
embedBinder hint body = mkNLamHint (binderHint hint) (embedTerm body)

binderHint :: Hint -> Maybe SmallId
binderHint hint
    = case hint of
        first : rest
            | isAsciiLower first && all hintChar rest && Set.notMember hint reservedNamedIdentifiers -> Just hint
        _ -> Nothing
    where
        hintChar ch = isAsciiLower ch || isAsciiUpper ch || isDigit ch || ch == '_'

recoverLevel :: TermNode -> Either String Level
recoverLevel node
    = case node of
        NCon (DC (DC_Named "lz")) _ -> Right 0
        NApp (NCon (DC (DC_Named "ls")) _) level _ -> (+ 1) <$> recoverLevel level
        _ -> Left "not a level"

recoverTerm :: TermNode -> Either String Term
recoverTerm node
    = case node of
        NCon (DC (DC_Named "prop")) _ -> Right Prop
        NApp (NCon (DC (DC_Named "typ")) _) level _ -> Type <$> recoverLevel level
        NApp (NCon (DC (DC_Named "cst")) _) (NCon (DC (DC_NatL c)) _) _ -> Right (Cst c)
        NIdx i -> Right (Var i)
        NApp (NApp (NCon (DC (DC_Named "prod")) _) a _) (NLam x _ b _) _ -> Pi (recoverHint x) <$> recoverTerm a <*> recoverTerm b
        NApp (NApp (NCon (DC (DC_Named "lam")) _) a _) (NLam x _ t _) _ -> Lam (recoverHint x) <$> recoverTerm a <*> recoverTerm t
        NApp (NApp (NApp (NCon (DC (DC_Named "letin")) _) t _) a _) (NLam x _ u _) _ -> Let (recoverHint x) <$> recoverTerm t <*> recoverTerm a <*> recoverTerm u
        NApp (NApp (NCon (DC (DC_Named "app")) _) t _) u _ -> App <$> recoverTerm t <*> recoverTerm u
        _ -> Left ("not a Core term: " ++ display node)

recoverHint :: Maybe SmallId -> Hint
recoverHint = maybe "" id

recoverList :: TermNode -> Either String [TermNode]
recoverList node
    = case node of
        NCon (DC DC_Nil) _ -> Right []
        NApp (NCon (DC DC_Nil) _) _ _ -> Right []
        NApp (NApp (NCon (DC DC_Cons) _) x _) xs _ -> (x :) <$> recoverList xs
        NApp (NApp (NApp (NCon (DC DC_Cons) _) _ _) x _) xs _ -> (x :) <$> recoverList xs
        _ -> Left "not a list"

recoverString :: TermNode -> Either String String
recoverString node = recoverList node >>= mapM character where
    character (NCon (DC (DC_ChrL ch)) _) = Right ch
    character _ = Left "not a character"

-- A report may mention the local variables of the rule that failed, so its terms are kept as text.
recoverReport :: TermNode -> Either String Report
recoverReport node
    = case node of
        NApp (NApp (NCon (DC (DC_Named "rep")) _) rule _) args _ -> Report <$> recoverString rule <*> (map display <$> recoverList args)
        _ -> Left "not a report"

display :: TermNode -> String
display node = prettyTerm Notation.initial initialCache node ""

cstTypeFact :: ConstId -> Term -> TermNode
cstTypeFact c a = foldlNApp (named "cst_type") [natural c, embedTerm a]

cstBodyFact :: ConstId -> Term -> TermNode
cstBodyFact c t = foldlNApp (named "cst_body") [natural c, embedTerm t]

admitAxGoal :: Term -> TermNode
admitAxGoal a = mkNApp (named "admit_ax") (embedTerm a)

admitDefGoal :: Term -> Term -> TermNode
admitDefGoal a t = foldlNApp (named "admit_def") [embedTerm a, embedTerm t]

typeGoal :: Term -> LogicVar -> TermNode
typeGoal t output = foldlNApp (named "infer") [embedTerm t, mkLVar output]

normalGoal :: Term -> LogicVar -> TermNode
normalGoal t output = foldlNApp (named "norm") [embedTerm t, mkLVar output]
