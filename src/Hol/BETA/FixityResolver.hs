module Hol.BETA.FixityResolver
    ( FixityError (..)
    , resolveTermWithFixity
    , resolveDeclsWithFixity
    ) where

import Hol.BETA.Header
import Hol.BETA.Notation (NotationDB, FixityKind (..), Precedence)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.PlanHolLexer
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map

data FixityError
    = FixityError SLoc String
    deriving (Eq, Show)

data Piece
    = PAtom TermRep
    | POper SLoc SmallId DataConstructor
    deriving ()

data FixityOrigin
    = FixityOrigin SLoc SmallId (FixityKind, Precedence)
    deriving ()

appPrec :: Precedence
appPrec = 10

maxFixityPrec :: Precedence
maxFixityPrec = appPrec - 1

resolveDeclsWithFixity :: NotationDB -> [DeclRep] -> Either FixityError [DeclRep]
resolveDeclsWithFixity db0 decls0 = do
    db <- collectModuleFixities db0 decls0
    traverse (resolveDecl db) decls0

resolveDecl :: NotationDB -> DeclRep -> Either FixityError DeclRep
resolveDecl db decl
    = case decl of
        RFactDecl loc term -> RFactDecl loc <$> resolveTermWithFixity db term
        RNotationDecl loc name params body -> RNotationDecl loc name params <$> resolveTermWithFixity db body
        _ -> Right decl

collectModuleFixities :: NotationDB -> [DeclRep] -> Either FixityError NotationDB
collectModuleFixities db0 decls = snd <$> foldM step (Map.empty, db0) decls where
    step (local, db) decl = case decl of
        RFixityDecl loc form name prec -> do
            checkFixityPrecedence loc prec
            let fp@(kind, precedence) = (toKind form, fromInteger prec)
            checkImportedFixity db0 loc name fp
            checkLocalFixity local loc name fp
            let origin = FixityOrigin loc name fp
                local' = foldr (`Map.insert` origin) local (Notation.fixityAliases name)
            return (local', Notation.addFixity name kind precedence db)
        _ -> return (local, db)

checkFixityPrecedence :: SLoc -> Integer -> Either FixityError ()
checkFixityPrecedence loc precedence
    | 0 <= precedence && precedence <= toInteger maxFixityPrec = Right ()
    | otherwise = Left (FixityError loc ("Fixity precedence must be between 0 and " ++ show maxFixityPrec ++ "."))

checkImportedFixity :: NotationDB -> SLoc -> SmallId -> (FixityKind, Precedence) -> Either FixityError ()
checkImportedFixity db loc name fp = mapM_ check (Notation.fixityAliases name) where
    check alias = case Notation.lookupFixity alias db of
        Just importedFp
            | importedFp /= fp
            , Notation.lookupFixity alias Notation.initial /= Just importedFp ->
                Left (FixityError loc ("Fixity declaration for `" ++ name ++ "' conflicts with an imported fixity."))
        _ -> Right ()

checkLocalFixity :: Map.Map SmallId FixityOrigin -> SLoc -> SmallId -> (FixityKind, Precedence) -> Either FixityError ()
checkLocalFixity local loc name fp = mapM_ check (Notation.fixityAliases name) where
    check alias = case Map.lookup alias local of
        Just (FixityOrigin _ priorName priorFp)
            | priorFp /= fp ->
                Left (FixityError loc ("Conflicting fixity declarations for `" ++ name ++ "' and `" ++ priorName ++ "'."))
        _ -> Right ()

toKind :: FixityForm -> FixityKind
toKind FF_InfixL = FK_InfixL
toKind FF_InfixR = FK_InfixR
toKind FF_InfixN = FK_InfixN
toKind FF_Prefix = FK_Prefix

resolveTermWithFixity :: NotationDB -> TermRep -> Either FixityError TermRep
resolveTermWithFixity db term = do
    pieces <- flattenTerm db term
    case parseExpr db 0 Nothing (getSLoc term) pieces of
        Left err -> Left err
        Right (term', []) -> Right term'
        Right (_, piece : _) -> Left (FixityError (pieceLoc piece) "Unexpected operator while resolving fixity.")

flattenTerm :: NotationDB -> TermRep -> Either FixityError [Piece]
flattenTerm db term
    = case term of
        RPrn loc body -> do
            body' <- resolveTermWithFixity db body
            return [PAtom (RPrn loc body')]
        RAbs loc name body -> do
            body' <- resolveTermWithFixity db body
            return [PAtom (RAbs loc name body')]
        RApp _ (RApp _ oper lhs) rhs
            | Just (opLoc, name, con) <- operatorTerm oper
            , Just (kind, _) <- operatorFixity db con name
            , isInfix kind -> do
                lhsPieces <- flattenTerm db lhs
                rhsPieces <- flattenTerm db rhs
                return (lhsPieces ++ [POper opLoc name con] ++ rhsPieces)
        RApp _ _ _ -> flattenApp db term
        _ -> return [atomOrOper db term]

flattenApp :: NotationDB -> TermRep -> Either FixityError [Piece]
flattenApp db term = traverse atomOrOperM (collectApps term) where
    atomOrOperM part = case atomOrOper db part of
        PAtom part' -> PAtom <$> resolveTermWithFixity db part'
        oper -> Right oper

collectApps :: TermRep -> [TermRep]
collectApps (RApp _ lhs rhs) = collectApps lhs ++ [rhs]
collectApps term = [term]

atomOrOper :: NotationDB -> TermRep -> Piece
atomOrOper db term
    = case operatorTerm term of
        Just (loc, name, con)
            | Just _ <- operatorFixity db con name -> POper loc name con
        _ -> PAtom term

-- Seeded fixities belong to primitive constructors.  A quoted reserved name
-- is represented by @DC_Named@ after parsing, and must not accidentally inherit
-- the primitive's fixity merely because both use the same text (for example
-- named `` `pi` `` versus logical @pi@).  Named constructors participate only
-- through an explicit local/imported fixity declaration.
operatorFixity :: NotationDB -> DataConstructor -> SmallId -> Maybe (FixityKind, Precedence)
operatorFixity db con name = case con of
    DC_Named _ -> lookup name (Notation.declaredFixityList db)
    _ -> Notation.lookupFixity name db

parseExpr :: NotationDB -> Precedence -> Maybe (Precedence, FixityKind) -> SLoc -> [Piece] -> Either FixityError (TermRep, [Piece])
parseExpr db minPrec used missingOperandLoc pieces0 = do
    (left, pieces1) <- parsePrefixOrAtom db missingOperandLoc pieces0
    parseRest db minPrec used left pieces1

parsePrefixOrAtom :: NotationDB -> SLoc -> [Piece] -> Either FixityError (TermRep, [Piece])
parsePrefixOrAtom _ missingOperandLoc []
    = Left (FixityError missingOperandLoc "Unexpected end of expression while resolving fixity.")
parsePrefixOrAtom db _ (piece : pieces)
    = case piece of
        POper loc name con
            | Just (FK_Prefix, prec) <- operatorFixity db con name -> do
                (arg, rest) <- parseExpr db prec Nothing loc pieces
                return (RApp (loc <> getSLoc arg) (RCon loc con) arg, rest)
            | otherwise -> return (RCon loc con, pieces)
        PAtom atom -> return (atom, pieces)

parseRest :: NotationDB -> Precedence -> Maybe (Precedence, FixityKind) -> TermRep -> [Piece] -> Either FixityError (TermRep, [Piece])
parseRest db minPrec used left pieces
    = case pieces of
        POper loc name con : rest
            | Just (kind, prec) <- operatorFixity db con name, isInfix kind, prec >= minPrec -> do
                checkSameLevel loc used prec kind
                let rhsMin = case kind of
                        FK_InfixR -> prec
                        _ -> prec + 1
                    rhsUsed = case kind of
                        FK_InfixR -> Just (prec, kind)
                        _ -> Nothing
                (right, rest') <- parseExpr db rhsMin rhsUsed loc rest
                let left' = applyOperator loc con left right
                parseRest db minPrec (Just (prec, kind)) left' rest'
        piece : rest
            | canStartAtom db piece, appPrec >= minPrec -> do
                (arg, rest') <- parsePrefixOrAtom db (pieceLoc piece) (piece : rest)
                let left' = RApp (getSLoc left <> getSLoc arg) left arg
                parseRest db minPrec used left' rest'
        _ -> Right (left, pieces)

checkSameLevel :: SLoc -> Maybe (Precedence, FixityKind) -> Precedence -> FixityKind -> Either FixityError ()
checkSameLevel _ Nothing _ _ = Right ()
checkSameLevel loc (Just (prec0, kind0)) prec kind
    | prec0 /= prec = Right ()
    | kind0 == FK_InfixL && kind == FK_InfixL = Right ()
    | kind0 == FK_InfixR && kind == FK_InfixR = Right ()
    | otherwise = Left (FixityError loc "Conflicting associativity at the same precedence.")

canStartAtom :: NotationDB -> Piece -> Bool
canStartAtom _ (PAtom _) = True
canStartAtom db (POper _ name con)
    = case operatorFixity db con name of
        Just (FK_InfixL, _) -> False
        Just (FK_InfixR, _) -> False
        Just (FK_InfixN, _) -> False
        _ -> True

isInfix :: FixityKind -> Bool
isInfix FK_InfixL = True
isInfix FK_InfixR = True
isInfix FK_InfixN = True
isInfix FK_Prefix = False

applyOperator :: SLoc -> DataConstructor -> TermRep -> TermRep -> TermRep
applyOperator loc con lhs rhs
    = RApp (getSLoc lhs <> getSLoc rhs) (RApp (getSLoc lhs <> loc) (RCon loc con) lhs) rhs

pieceLoc :: Piece -> SLoc
pieceLoc (PAtom term) = getSLoc term
pieceLoc (POper loc _ _) = loc

operatorTerm :: TermRep -> Maybe (SLoc, SmallId, DataConstructor)
operatorTerm (RCon loc dataConstructor)
    = case dataConstructor of
        DC_LO LO_if -> found ":-"
        DC_LO LO_or -> found ";"
        DC_LO LO_imply -> found "=>"
        DC_LO LO_and -> found "&"
        DC_LO LO_pi -> found "pi"
        DC_LO LO_sigma -> found "sigma"
        DC_LO LO_is -> found "is"
        DC_eq -> found "="
        DC_le -> found "=<"
        DC_lt -> found "<"
        DC_ge -> found ">="
        DC_gt -> found ">"
        DC_plus -> found "+"
        DC_minus -> found "-"
        DC_mul -> found "*"
        DC_div -> found "/"
        DC_Cons -> found "::"
        DC_Succ -> found "s"
        DC_Named name -> found name
        _ -> Nothing
      where
        found name = Just (loc, name, dataConstructor)
operatorTerm _ = Nothing
