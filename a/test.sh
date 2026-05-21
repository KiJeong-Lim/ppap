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
test -f "$workdir/cases/000001/native/build.log"

printf 'Project --fuzz --cases=3 --seed=10 --size=3 --workdir=.project-a-test-work\n\n' \
  | env -u PROJECT_A_TRANSLATOR cabal run -v0 ppap

test -f "$workdir/cases/000003/result.json"

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

printf 'Project --shrink --case-dir=.project-a-test-work/objective/cases/000001\n\n' \
  | PROJECT_A_TRANSLATOR="$translator" cabal run -v0 ppap

test -f "$objective_workdir/cases/000001/shrunk/report.txt"
grep -q 'objective-drop: nodes 82 -> 3, repr 981 -> 27' "$objective_workdir/cases/000001/shrunk/report.txt"
