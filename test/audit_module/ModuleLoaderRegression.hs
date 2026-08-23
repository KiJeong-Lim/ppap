module Main where

import Control.Exception (bracket)
import Control.Monad (unless)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Hol.BETA.Diagnostic (DiagnosticMode (DiagnosticTest))
import Hol.BETA.Header (DataConstructor (..), KindExpr (..), TypeConstructor (..))
import Hol.BETA.ModuleLoader
import qualified Hol.BETA.Notation as Notation
import System.Directory
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>), takeDirectory)
import Z.Utils (execUniqueT)

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("module loader regression failed: " ++ label)
    exitFailure

initialKinds :: Map.Map TypeConstructor KindExpr
initialKinds = Map.fromList
    [ (TC_Arrow, KArr Star (KArr Star Star))
    , (TC_Named "o", Star)
    , (TC_Named "nat", Star)
    , (TC_Named "char", Star)
    ]

loadResult :: FilePath -> IO (Either String LoadedModule)
loadResult path = execUniqueT (loadMainWithDiagnostic DiagnosticTest initialKinds Map.empty [] path)

loadModule :: FilePath -> IO LoadedModule
loadModule path = do
    loaded <- loadResult path
    case loaded of
        Left err -> do
            putStrLn err
            exitFailure
        Right result -> return result

expectLoadFailure :: String -> [String] -> FilePath -> IO ()
expectLoadFailure label fragments path = do
    loaded <- loadResult path
    case loaded of
        Left err -> assert label (all (`isInfixOf` err) fragments)
        Right _ -> assert label False

writeModule :: FilePath -> String -> IO ()
writeModule path source = do
    createDirectoryIfMissing True (takeDirectory path)
    writeFile path source

hasKind :: String -> ModuleEnv -> Bool
hasKind name env = Map.member (TC_Named name) (moduleEnvKinds env)

hasType :: String -> ModuleEnv -> Bool
hasType name env = Map.member (DC_Named name) (moduleEnvTypes env)

main :: IO ()
main = do
    [root, scratch, locator] <- getArgs
    let rootChoice = root </> locator ++ ".hol"
        localChoice = scratch </> locator ++ ".hol"
        precedenceMain = scratch </> "precedence_main.hol"
    rootChoiceExists <- doesPathExist rootChoice
    assert "temporary root candidate collided with an existing file" (not rootChoiceExists)
    bracket
        (writeModule rootChoice "kind chosen_from_root type.\n")
        (const (removeFile rootChoice))
        (\_ -> do
            writeModule localChoice "kind chosen_from_importer type.\n"
            writeModule precedenceMain ("import " ++ locator ++ ".\n")
            loaded <- loadModule precedenceMain
            let env = loadedMain loaded
            assert "importer-directory candidate did not win" (hasKind "chosen_from_importer" env)
            assert "project-root fallback was loaded despite a local candidate" (not (hasKind "chosen_from_root" env)))

    let tree = scratch </> "tree"
        diamondMain = tree </> "main.hol"
        leftImporter = tree </> "left" </> "importer.hol"
        rightImporter = tree </> "right" </> "importer.hol"
        leftShared = tree </> "left" </> "shared.hol"
        rightShared = tree </> "right" </> "shared.hol"
    writeModule diamondMain "import left.importer.\nimport right.importer.\n"
    writeModule leftImporter "import shared.\n"
    writeModule rightImporter "import shared.\n"
    writeModule leftShared "kind left_shared_identity type.\n"
    writeModule rightShared "kind right_shared_identity type.\n"
    diamond <- loadModule diamondMain
    leftCanonical <- canonicalizePath leftShared
    rightCanonical <- canonicalizePath rightShared
    assert "left importer-local shared module was not loaded" (Map.member leftCanonical (loadedAll diamond))
    assert "right importer-local shared module was collapsed into the left module" (Map.member rightCanonical (loadedAll diamond))

    let reloadMain = scratch </> "reload_main.hol"
        reloadDep = scratch </> "reload_dep.hol"
    writeModule reloadMain "import reload_dep.\n"
    writeModule reloadDep "kind reload_before type.\n"
    before <- loadModule reloadMain
    assert "initial imported content was not loaded" (hasKind "reload_before" (loadedMain before))
    writeModule reloadDep "kind reload_after type.\n"
    after <- loadModule reloadMain
    assert "stale imported content survived reload" (not (hasKind "reload_before" (loadedMain after)))
    assert "changed imported content was not observed on reload" (hasKind "reload_after" (loadedMain after))

    let missingMain = scratch </> "missing_main.hol"
        missingImportLine = "    import audit_module_that_does_not_exist."
        missingSource = "% Preserve the import declaration's exact source location.\n" ++ missingImportLine ++ "\n"
    writeModule missingMain missingSource
    missingCanonical <- canonicalizePath missingMain
    let missingLocation = missingCanonical ++ ":2:5-2:" ++ show (length missingImportLine)
    expectLoadFailure "missing import diagnostic did not use the import declaration location"
        [missingLocation, "Cannot resolve module"] missingMain

    let identical = scratch </> "identical"
        identicalKindMain = identical </> "kind_main.hol"
        identicalKindLeft = identical </> "kind_left.hol"
        identicalKindRight = identical </> "kind_right.hol"
    writeModule identicalKindMain "import kind_left.\nimport kind_right.\n"
    writeModule identicalKindLeft "kind shared_kind type.\n"
    writeModule identicalKindRight "kind shared_kind type.\n"
    identicalKinds <- loadModule identicalKindMain
    assert "identical imported kinds did not collapse" (hasKind "shared_kind" (loadedMain identicalKinds))

    let identicalTypeMain = identical </> "type_main.hol"
        identicalTypeLeft = identical </> "type_left.hol"
        identicalTypeRight = identical </> "type_right.hol"
    writeModule identicalTypeMain "import type_left.\nimport type_right.\n"
    writeModule identicalTypeLeft "type shared_poly (A -> A -> o).\n"
    writeModule identicalTypeRight "type shared_poly (B -> B -> o).\n"
    identicalTypes <- loadModule identicalTypeMain
    assert "alpha-equivalent imported polytypes did not collapse" (hasType "shared_poly" (loadedMain identicalTypes))

    let identicalFixityMain = identical </> "fixity_main.hol"
        identicalFixityLeft = identical </> "fixity_left.hol"
        identicalFixityRight = identical </> "fixity_right.hol"
    writeModule identicalFixityMain "import fixity_left.\nimport fixity_right.\n"
    writeModule identicalFixityLeft "infixl shared_fixity 6.\n"
    writeModule identicalFixityRight "infixl shared_fixity 6.\n"
    identicalFixities <- loadModule identicalFixityMain
    assert "identical imported fixities did not collapse"
        (Notation.lookupFixity "shared_fixity" (moduleEnvNotation (loadedMain identicalFixities)) == Just (Notation.FK_InfixL, 6))

    let conflicts = scratch </> "conflicts"
        kindMain = conflicts </> "kind_main.hol"
        kindLeft = conflicts </> "kind_left.hol"
        kindRight = conflicts </> "kind_right.hol"
    writeModule kindMain "import kind_left.\nimport kind_right.\n"
    writeModule kindLeft "kind conflict_kind type.\n"
    writeModule kindRight "kind conflict_kind (type -> type).\n"
    expectLoadFailure "conflicting imported kind diagnostic omitted a declaration origin"
        [ "Import inconsistency (C1)"
        , pathDerivedName root kindLeft
        , pathDerivedName root kindRight
        ] kindMain

    let typeMain = conflicts </> "type_main.hol"
        typeLeft = conflicts </> "type_left.hol"
        typeRight = conflicts </> "type_right.hol"
    writeModule typeMain "import type_left.\nimport type_right.\n"
    writeModule typeLeft "type conflict_type (nat -> o).\n"
    writeModule typeRight "type conflict_type (char -> o).\n"
    expectLoadFailure "conflicting imported polytype diagnostic omitted a declaration origin"
        [ "Import inconsistency (C2)"
        , pathDerivedName root typeLeft
        , pathDerivedName root typeRight
        ] typeMain

    let notationMain = conflicts </> "notation_main.hol"
        notationLeft = conflicts </> "notation_left.hol"
        notationRight = conflicts </> "notation_right.hol"
        notationSeed = "kind conflict_obj type.\ntype conflict_a conflict_obj.\ntype conflict_b conflict_obj.\n"
    writeModule notationMain "import notation_left.\nimport notation_right.\n"
    writeModule notationLeft (notationSeed ++ "notation conflict_notation := conflict_a.\n")
    writeModule notationRight (notationSeed ++ "notation conflict_notation := conflict_b.\n")
    expectLoadFailure "conflicting imported notation diagnostic omitted a declaration origin"
        [ "Import inconsistency (C4)"
        , pathDerivedName root notationLeft
        , pathDerivedName root notationRight
        ] notationMain

    putStrLn "module loader path/reload regressions passed"
