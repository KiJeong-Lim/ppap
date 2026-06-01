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
grep -q 'var msg string' "$workdir/randomgen.out"
grep -q 'fmt.Scan(&msg)' "$workdir/randomgen.out"
grep -q 'fmt.Print(.*msg' "$workdir/randomgen.out"

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
main = putStr "3"
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
main = pure ()
HASKELL

printf '(* Project A mismatch smoke test. *)\n'
EOF
chmod +x "$translator"

objective_workdir="$workdir/objective"
printf 'Project --one --seed=42 --size=6 --workdir=.project-a-test-work/objective\n\n' \
  | PROJECT_A_TRANSLATOR="$translator" cabal run -v0 ppap

grep -q 'UsesZeroInit' "$objective_workdir/cases/000001/feature.json"

printf 'Project --shrink --case-dir=.project-a-test-work/objective/cases/000001\n\n' \
  | PROJECT_A_TRANSLATOR="$translator" cabal run -v0 ppap

test -f "$objective_workdir/cases/000001/shrunk/report.txt"
test -f "$objective_workdir/regressions/000001/report.txt"
grep -q 'shrunk-status: CaseFail' "$objective_workdir/cases/000001/shrunk/report.txt"
grep -q 'objective-drop:' "$objective_workdir/cases/000001/shrunk/report.txt"

string_tool_root="${PROJECT_A_TOOL_ROOT:-/home/lim/Desktop/GoCris/go2c}"
string_golanggen_root="${PROJECT_A_GOLANGGEN_ROOT:-$string_tool_root/golanggen}"
string_opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-$string_tool_root}"
string_coqc="${PROJECT_A_COQC:-}"
if [[ -z "$string_coqc" && -x /home/lim/Desktop/GoCris/_opam/bin/coqc ]]; then
  string_coqc="/home/lim/Desktop/GoCris/_opam/bin/coqc"
fi

if [[ -d "$string_golanggen_root" && -f "$string_tool_root/_CoqProject" ]]; then
  string_src_dir="$workdir/string-io-src"
  mkdir -p "$string_src_dir"
  cat > "$string_src_dir/string_io.go" <<'EOF'
package main

import "fmt"

func main() {
	var s string
	fmt.Scan(&s)
	fmt.Print(7, s, false)
}
EOF

  string_args=(
    "--no-build"
    "--workdir=$workdir/string-io"
    "--translator=$PWD/a/golanggen-translator.sh"
    "--extract-mode=mod"
    "--tool-root=$string_tool_root"
    "--mod=Input.project_a_mod"
    "--coqproject=$string_tool_root/_CoqProject"
    "--opam-env-dir=$string_opam_env_dir"
    "--ghc-args=${PROJECT_A_GHC_ARGS:--fdefer-type-errors,-Wno-deferred-type-errors}"
    "--stdin=go"
  )

  if [[ -n "$string_coqc" ]]; then
    string_args+=("--coqc=$string_coqc")
  fi

  PROJECT_A_GOLANGGEN_ROOT="$string_golanggen_root" \
    a/go-dir-diff.sh "${string_args[@]}" "$string_src_dir"

  grep -q '"stdout": "7gofalse"' "$workdir/string-io/cases/000001/result.json"

  neg_int_src_dir="$workdir/neg-int-io-src"
  mkdir -p "$neg_int_src_dir"
  cat > "$neg_int_src_dir/neg_int_io.go" <<'EOF'
package main

import "fmt"

func main() {
	var x int
	fmt.Scan(&x)
	fmt.Print(x)
}
EOF

  neg_int_args=(
    "--no-build"
    "--workdir=$workdir/neg-int-io"
    "--translator=$PWD/a/golanggen-translator.sh"
    "--extract-mode=mod"
    "--tool-root=$string_tool_root"
    "--mod=Input.project_a_mod"
    "--coqproject=$string_tool_root/_CoqProject"
    "--opam-env-dir=$string_opam_env_dir"
    "--ghc-args=${PROJECT_A_GHC_ARGS:--fdefer-type-errors,-Wno-deferred-type-errors}"
    "--stdin=-12"
  )

  if [[ -n "$string_coqc" ]]; then
    neg_int_args+=("--coqc=$string_coqc")
  fi

  PROJECT_A_GOLANGGEN_ROOT="$string_golanggen_root" \
    a/go-dir-diff.sh "${neg_int_args[@]}" "$neg_int_src_dir"

  grep -q '"stdout": "-12"' "$workdir/neg-int-io/cases/000001/result.json"
else
  echo "skip: string IO e2e requires go2c/golanggen under $string_tool_root"
fi
