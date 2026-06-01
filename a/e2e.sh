#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/e2e.sh [options]

Options:
  --mode=one|fuzz|search  Default: one
  --cases=N               Default: 1
  --seed=N                Default: 1
  --size=N                Default: 0
  --workdir=DIR           Default: .project-a-e2e-work
  --tool-root=DIR         Default: PROJECT_A_TOOL_ROOT or the value injected by a/boot.sh
  --golanggen-root=DIR    Default: PROJECT_A_GOLANGGEN_ROOT or tool-root/golanggen
  --coqproject=FILE       Default: PROJECT_A_COQPROJECTS or tool-root/_CoqProject
  --opam-env-dir=DIR      Default: PROJECT_A_OPAM_ENV_DIR or tool-root
  --coqc=COQC             Default: PROJECT_A_COQC or coqc
  --ghc-args=ARGS         Default: PROJECT_A_GHC_ARGS or -fdefer-type-errors,-Wno-deferred-type-errors
  --no-build              Skip cabal build.
  --tool-build            Build go2c Coq library before running.
  --no-tool-build         Skip go2c Coq library build. Default.
  -h, --help              Show this help.

Runs the stage-one Project A E2E path:
  generated Go -> golanggen Coq -> Coq extraction -> Haskell execution -> comparison.

It also runs fixed Go-file E2E smoke cases for string input/output and
negative integer input/output.

After a run, the script prints the generated source and extraction artifact
paths, including the extracted Haskell file.
EOF
}

print_artifact() {
  local label="$1"
  local path="$2"
  if [[ -f "$path" ]]; then
    printf '  %-20s %s\n' "$label:" "$path"
  fi
}

print_case_artifacts() {
  local case_dir="$1"
  if [[ ! -d "$case_dir" ]]; then
    return 0
  fi

  printf '\nartifacts: %s\n' "$case_dir"
  print_artifact "go" "$case_dir/gofile.go"
  print_artifact "coq" "$case_dir/coq/gofile.v"
  print_artifact "extracted hs" "$case_dir/coq/mod-extract/coq/extracted/ExtractedMain.hs"
  print_artifact "hs driver" "$case_dir/coq/mod-extract/coq/extracted/Main.hs"
  print_artifact "direct hs" "$case_dir/coq/extracted/Gofile.hs"
  print_artifact "result" "$case_dir/result.json"
}

print_artifacts() {
  local max_case="$cases"
  if [[ "$mode" == "one" ]]; then
    max_case=1
  fi

  local case_id
  local case_dir
  for ((case_id = 1; case_id <= max_case; case_id++)); do
    printf -v case_dir '%s/cases/%06d' "$workdir" "$case_id"
    print_case_artifacts "$case_dir"
  done
}

run_go_dir_smoke_case() {
  local label="$1"
  local source_dir="$2"
  local smoke_workdir="$3"
  local stdin_text="$4"
  local expected_stdout="$5"
  local smoke_args=(
    "--no-build"
    "--workdir=$smoke_workdir"
    "--translator=$repo_root/a/golanggen-translator.sh"
    "--extract-mode=mod"
    "--tool-root=$tool_root"
    "--mod=Input.project_a_mod"
    "--coqproject=$coqproject"
    "--opam-env-dir=$opam_env_dir"
    "--stdin=$stdin_text"
  )

  if [[ -n "$coqc_command" ]]; then
    smoke_args+=("--coqc=$coqc_command")
  fi

  if [[ -n "$ghc_args" ]]; then
    smoke_args+=("--ghc-args=$ghc_args")
  fi

  printf '\nfixed e2e smoke: %s\n' "$label"
  PROJECT_A_GOLANGGEN_ROOT="$golanggen_root" \
    "$repo_root/a/go-dir-diff.sh" "${smoke_args[@]}" "$source_dir"

  grep -Fq "\"stdout\": \"$expected_stdout\"" "$smoke_workdir/cases/000001/result.json"
  print_case_artifacts "$smoke_workdir/cases/000001"
}

run_fixed_io_smoke_cases() {
  local string_source_dir="$workdir/fixed-string-io-src"
  local neg_int_source_dir="$workdir/fixed-neg-int-io-src"

  mkdir -p "$string_source_dir" "$neg_int_source_dir"

  cat > "$string_source_dir/string_io.go" <<'EOF'
package main

import "fmt"

func main() {
	var s string
	fmt.Scan(&s)
	fmt.Print(7, s, false)
}
EOF

  cat > "$neg_int_source_dir/neg_int_io.go" <<'EOF'
package main

import "fmt"

func main() {
	var x int
	fmt.Scan(&x)
	fmt.Print(x)
}
EOF

  run_go_dir_smoke_case \
    "string input/output" \
    "$string_source_dir" \
    "$workdir/fixed-string-io" \
    "go" \
    "7gofalse"

  run_go_dir_smoke_case \
    "negative integer input/output" \
    "$neg_int_source_dir" \
    "$workdir/fixed-neg-int-io" \
    "-12" \
    "-12"
}

repo_root="$(cd "$(dirname "$0")/.." && pwd)"

# Local path defaults. Edit these when your go2c/golanggen checkout lives
# somewhere else; CLI flags and PROJECT_A_* environment variables still win.
default_tool_root="__PROJECT_A_BOOT_TOOL_ROOT__"
default_golanggen_root=

mode="${PROJECT_A_RUN_MODE:-one}"
cases="${PROJECT_A_CASES:-1}"
seed="${PROJECT_A_SEED:-1}"
size="${PROJECT_A_SIZE:-0}"
workdir="${PROJECT_A_WORKDIR:-.project-a-e2e-work}"
tool_root="${PROJECT_A_TOOL_ROOT:-$default_tool_root}"
golanggen_root="${PROJECT_A_GOLANGGEN_ROOT:-$default_golanggen_root}"
unbooted_tool_root="__PROJECT_A_BOOT_"'TOOL_ROOT__'
coqproject="${PROJECT_A_COQPROJECTS:-}"
opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-}"
coqc_command="${PROJECT_A_COQC:-}"
ghc_args="${PROJECT_A_GHC_ARGS:--fdefer-type-errors,-Wno-deferred-type-errors}"
do_build=1
do_tool_build="${PROJECT_A_E2E_TOOL_BUILD:-0}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
      usage
      exit 0
      ;;
    --no-build)
      do_build=0
      shift
      ;;
    --no-tool-build)
      do_tool_build=0
      shift
      ;;
    --tool-build)
      do_tool_build=1
      shift
      ;;
    --mode=*)
      mode="${1#*=}"
      shift
      ;;
    --mode)
      mode="${2:?missing value for --mode}"
      shift 2
      ;;
    --cases=*)
      cases="${1#*=}"
      shift
      ;;
    --cases)
      cases="${2:?missing value for --cases}"
      shift 2
      ;;
    --seed=*)
      seed="${1#*=}"
      shift
      ;;
    --seed)
      seed="${2:?missing value for --seed}"
      shift 2
      ;;
    --size=*)
      size="${1#*=}"
      shift
      ;;
    --size)
      size="${2:?missing value for --size}"
      shift 2
      ;;
    --workdir=*)
      workdir="${1#*=}"
      shift
      ;;
    --workdir)
      workdir="${2:?missing value for --workdir}"
      shift 2
      ;;
    --tool-root=*)
      tool_root="${1#*=}"
      shift
      ;;
    --tool-root)
      tool_root="${2:?missing value for --tool-root}"
      shift 2
      ;;
    --golanggen-root=*)
      golanggen_root="${1#*=}"
      shift
      ;;
    --golanggen-root)
      golanggen_root="${2:?missing value for --golanggen-root}"
      shift 2
      ;;
    --coqproject=*)
      coqproject="${1#*=}"
      shift
      ;;
    --coqproject)
      coqproject="${2:?missing value for --coqproject}"
      shift 2
      ;;
    --opam-env-dir=*)
      opam_env_dir="${1#*=}"
      shift
      ;;
    --opam-env-dir)
      opam_env_dir="${2:?missing value for --opam-env-dir}"
      shift 2
      ;;
    --coqc=*)
      coqc_command="${1#*=}"
      shift
      ;;
    --coqc)
      coqc_command="${2:?missing value for --coqc}"
      shift 2
      ;;
    --ghc-args=*)
      ghc_args="${1#*=}"
      shift
      ;;
    --ghc-args)
      ghc_args="${2:?missing value for --ghc-args}"
      shift 2
      ;;
    --*)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      echo "error: unexpected argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ -z "$golanggen_root" ]]; then
  golanggen_root="$tool_root/golanggen"
fi

if [[ "$tool_root" == "$unbooted_tool_root" ]]; then
  echo "error: this checkout has not been booted; run a/boot.sh or set PROJECT_A_TOOL_ROOT" >&2
  exit 2
fi

if [[ -z "$coqproject" ]]; then
  coqproject="$tool_root/_CoqProject"
fi

if [[ -z "$opam_env_dir" ]]; then
  opam_env_dir="$tool_root"
fi

if [[ "$do_tool_build" -eq 1 ]]; then
  if [[ ! -f "$tool_root/CoqMakefile" ]]; then
    echo "error: expected go2c CoqMakefile does not exist: $tool_root/CoqMakefile" >&2
    exit 2
  fi

  (
    cd "$opam_env_dir"
    eval "$(opam env)"
    cd "$tool_root"
    make -f CoqMakefile \
      theories/golang_notation.vo \
      theories/expr_sem.vo \
      theories/golang_builtins.vo \
      theories/stmt_sem.vo
  )
fi

run_args=(
  "--mode=$mode"
  "--cases=$cases"
  "--seed=$seed"
  "--size=$size"
  "--workdir=$workdir"
  "--translator=$repo_root/a/golanggen-translator.sh"
  "--tool-root=$tool_root"
  "--mod=Input.project_a_mod"
  "--coqproject=$coqproject"
  "--opam-env-dir=$opam_env_dir"
)

if [[ -n "$coqc_command" ]]; then
  run_args+=("--coqc=$coqc_command")
fi

if [[ -n "$ghc_args" ]]; then
  run_args+=("--ghc-args=$ghc_args")
fi

if [[ "$do_build" -eq 0 ]]; then
  run_args+=("--no-build")
fi

cd "$repo_root"
PROJECT_A_GOLANGGEN_ROOT="$golanggen_root" a/run.sh "${run_args[@]}"
print_artifacts
run_fixed_io_smoke_cases
