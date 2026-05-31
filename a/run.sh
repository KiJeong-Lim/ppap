#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/run.sh [options]

Options:
  --mode=one|fuzz|search
                       Run one generated case, many generated cases, or
                       corpus-guided mutation search.
                       Default: PROJECT_A_RUN_MODE or fuzz
  --cases=N            Number of cases for fuzz mode.
                       Default: PROJECT_A_CASES or 10
  --seed=N             Initial generator seed.
                       Default: PROJECT_A_SEED or 1
  --size=N             Generator size.
                       Default: PROJECT_A_SIZE or 3
  --workdir=DIR        Project A work directory.
                       Default: PROJECT_A_WORKDIR or .project-a-work
  --translator=CMD     Command that reads gofile.go and writes generated Coq to stdout.
                       Default: PROJECT_A_TRANSLATOR
  --tool-root=DIR      Private tool checkout root.
                       Default: PROJECT_A_TOOL_ROOT or the value injected by a/boot.sh
  --mod=TERM           Mod.t term exposed by the generated Coq file.
                       Default: PROJECT_A_EXTRACT_MOD or Input.t
  --require=M1,M2      Extra Coq modules to Require Import before --mod.
                       Default: PROJECT_A_EXTRACT_REQUIRE
  --coqproject=FILE    _CoqProject file(s), comma-separated.
                       Default: PROJECT_A_COQPROJECTS or tool-root/_CoqProject
  --opam-env-dir=DIR   Directory where `opam env` should be evaluated.
                       Default: PROJECT_A_OPAM_ENV_DIR or tool-root
  --coqc=COQC          coqc command. Default: PROJECT_A_COQC or coqc
  --ghc-args=ARGS      Extra GHC args, comma-separated.
                       Default: PROJECT_A_GHC_ARGS
  --no-build           Skip `cabal build`.
  -h, --help           Show this help.

The translator contract is the same as Project A's runner contract: it receives
the generated `gofile.go` path as its last argument and must print a Coq file
that can be copied into the extraction harness as ProjectA.Input.
EOF
}

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
mode="${PROJECT_A_RUN_MODE:-fuzz}"
cases="${PROJECT_A_CASES:-10}"
seed="${PROJECT_A_SEED:-1}"
size="${PROJECT_A_SIZE:-3}"
workdir="${PROJECT_A_WORKDIR:-.project-a-work}"
translator="${PROJECT_A_TRANSLATOR:-}"
unbooted_tool_root="__PROJECT_A_BOOT_"'TOOL_ROOT__'
tool_root="${PROJECT_A_TOOL_ROOT:-__PROJECT_A_BOOT_TOOL_ROOT__}"
mod_term="${PROJECT_A_EXTRACT_MOD:-Input.t}"
requires="${PROJECT_A_EXTRACT_REQUIRE:-}"
coqproject="${PROJECT_A_COQPROJECTS:-}"
opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-}"
coqc_command="${PROJECT_A_COQC:-}"
ghc_args="${PROJECT_A_GHC_ARGS:-}"
do_build=1

reject_whitespace() {
  local name="$1"
  local value="$2"
  if [[ "$value" =~ [[:space:]] ]]; then
    echo "error: $name must not contain whitespace: $value" >&2
    exit 2
  fi
}

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
    --translator=*)
      translator="${1#*=}"
      shift
      ;;
    --translator)
      translator="${2:?missing value for --translator}"
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
    --mod=*)
      mod_term="${1#*=}"
      shift
      ;;
    --mod)
      mod_term="${2:?missing value for --mod}"
      shift 2
      ;;
    --require=*)
      requires="${1#*=}"
      shift
      ;;
    --require)
      requires="${2:?missing value for --require}"
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

case "$mode" in
  one|fuzz|search)
    ;;
  *)
    echo "error: --mode must be one, fuzz, or search: $mode" >&2
    exit 2
    ;;
esac

if [[ -z "$translator" ]]; then
  echo "error: --translator=CMD or PROJECT_A_TRANSLATOR is required" >&2
  exit 2
fi

if [[ "$tool_root" == "$unbooted_tool_root" ]]; then
  echo "error: this checkout has not been booted; run a/boot.sh or set PROJECT_A_TOOL_ROOT" >&2
  exit 2
fi

reject_whitespace "--mode" "$mode"
reject_whitespace "--cases" "$cases"
reject_whitespace "--seed" "$seed"
reject_whitespace "--size" "$size"
reject_whitespace "--workdir" "$workdir"
reject_whitespace "--tool-root" "$tool_root"
reject_whitespace "--mod" "$mod_term"
reject_whitespace "--require" "$requires"
reject_whitespace "--coqproject" "$coqproject"
reject_whitespace "--opam-env-dir" "$opam_env_dir"
reject_whitespace "--coqc" "$coqc_command"
reject_whitespace "--ghc-args" "$ghc_args"

cmd=(Project "--$mode" "--seed=$seed" "--size=$size" "--workdir=$workdir")

if [[ "$mode" == "fuzz" || "$mode" == "search" ]]; then
  cmd+=("--cases=$cases")
fi

env_args=(
  "PROJECT_A_TRANSLATOR=$translator"
  "PROJECT_A_EXTRACT_MODE=mod"
  "PROJECT_A_TOOL_ROOT=$tool_root"
  "PROJECT_A_EXTRACT_MOD=$mod_term"
)

if [[ -n "$requires" ]]; then
  env_args+=("PROJECT_A_EXTRACT_REQUIRE=$requires")
fi

if [[ -n "$coqproject" ]]; then
  env_args+=("PROJECT_A_COQPROJECTS=$coqproject")
fi

if [[ -n "$opam_env_dir" ]]; then
  env_args+=("PROJECT_A_OPAM_ENV_DIR=$opam_env_dir")
fi

if [[ -n "$coqc_command" ]]; then
  env_args+=("PROJECT_A_COQC=$coqc_command")
fi

if [[ -n "$ghc_args" ]]; then
  env_args+=("PROJECT_A_GHC_ARGS=$ghc_args")
fi

cd "$repo_root"

if [[ "$do_build" -eq 1 ]]; then
  cabal build
fi

printf '%s\n\n' "${cmd[*]}" | env "${env_args[@]}" cabal run -v0 ppap
