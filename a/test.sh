#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

workdir=".project-a-test-work"

rm -rf "$workdir"

cabal build

export PPAP_COLOR=always

printf 'Project --one --seed=1 --size=0 --workdir=.project-a-test-work\n\n' \
  | env -u PROJECT_A_TRANSLATOR cabal run -v0 ppap

test -f "$workdir/cases/000001/gofile.go"
test -f "$workdir/cases/000001/result.json"
test -f "$workdir/cases/000001/score.json"
test -f "$workdir/cases/000001/native/build.log"
test -f "$workdir/failures/000001/result.json"
test -f "$workdir/failures/000001/score.json"

a/randomgen.sh --cases=2 --seed=100 --size=4 --no-build > "$workdir/randomgen.out"
grep -q '^// randomgen case 1, seed=100, size=4$' "$workdir/randomgen.out"
grep -q '^// randomgen case 2, seed=101, size=4$' "$workdir/randomgen.out"
test "$(grep -c '^package main$' "$workdir/randomgen.out")" -eq 2

printf 'Project --fuzz --cases=3 --seed=10 --size=3 --workdir=.project-a-test-work\n\n' \
  | env -u PROJECT_A_TRANSLATOR cabal run -v0 ppap

test -f "$workdir/cases/000003/result.json"

pass_translator="$PWD/$workdir/pass-translator.sh"
cat > "$pass_translator" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

mkdir -p coq/extracted
cat > coq/extracted/Gofile.hs <<'HASKELL'
main :: IO ()
main = putStr "3\n"
HASKELL

printf '(* Project A local passing smoke test. *)\n'
EOF
chmod +x "$pass_translator"

printf 'Project --one --seed=1 --size=0 --workdir=.project-a-test-work/pass\n\n' \
  | PROJECT_A_TRANSLATOR="$pass_translator" cabal run -v0 ppap

test -f "$workdir/pass/cases/000001/score.json"
test -f "$workdir/pass/cases/000001/corpus.json"
test -f "$workdir/pass/corpus/cases/000001/score.json"

translator="$PWD/$workdir/mismatch-translator.sh"
cat > "$translator" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail

mkdir -p coq/extracted
cat > coq/extracted/Gofile.hs <<'HASKELL'
main :: IO ()
main = putStrLn "PROJECT_A_FAKE_MISMATCH"
HASKELL

printf '(* Project A local mismatch smoke test. *)\n'
EOF
chmod +x "$translator"

objective_workdir="$workdir/objective"
printf 'Project --one --seed=42 --size=6 --workdir=.project-a-test-work/objective\n\n' \
  | PROJECT_A_TRANSLATOR="$translator" cabal run -v0 ppap

grep -q 'UsesTypeDecl' "$objective_workdir/cases/000001/feature.json"
grep -q 'UsesStruct' "$objective_workdir/cases/000001/feature.json"
grep -q 'UsesPointer' "$objective_workdir/cases/000001/feature.json"
grep -q 'UsesField' "$objective_workdir/cases/000001/feature.json"

printf 'Project --shrink --case-dir=.project-a-test-work/objective/cases/000001\n\n' \
  | PROJECT_A_TRANSLATOR="$translator" cabal run -v0 ppap

test -f "$objective_workdir/cases/000001/shrunk/report.txt"
test -f "$objective_workdir/regressions/000001/report.txt"
grep -q 'objective-drop: nodes 203 -> 3, repr 2780 -> 30' "$objective_workdir/cases/000001/shrunk/report.txt"
