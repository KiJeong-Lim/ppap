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
  --tool-root=DIR         Default: PROJECT_A_TOOL_ROOT or /home/lim/coq82000/go2c
  --golanggen-root=DIR    Default: PROJECT_A_GOLANGGEN_ROOT or tool-root/golanggen
  --coqproject=FILE       Default: PROJECT_A_COQPROJECTS or tool-root/_CoqProject
  --opam-env-dir=DIR      Default: PROJECT_A_OPAM_ENV_DIR or tool-root
  --coqc=COQC             Default: PROJECT_A_COQC or coqc
  --ghc-args=ARGS         Default: PROJECT_A_GHC_ARGS or -fdefer-type-errors,-Wno-deferred-type-errors
  --no-build              Skip cabal build.
  -h, --help              Show this help.

Runs the stage-one Project A E2E path:
  generated Go -> golanggen Coq -> Coq extraction -> Haskell execution -> comparison.
EOF
}

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
mode="${PROJECT_A_RUN_MODE:-one}"
cases="${PROJECT_A_CASES:-1}"
seed="${PROJECT_A_SEED:-1}"
size="${PROJECT_A_SIZE:-0}"
workdir="${PROJECT_A_WORKDIR:-.project-a-e2e-work}"
tool_root="${PROJECT_A_TOOL_ROOT:-/home/lim/coq82000/go2c}"
golanggen_root="${PROJECT_A_GOLANGGEN_ROOT:-}"
coqproject="${PROJECT_A_COQPROJECTS:-}"
opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-}"
coqc_command="${PROJECT_A_COQC:-}"
ghc_args="${PROJECT_A_GHC_ARGS:--fdefer-type-errors,-Wno-deferred-type-errors}"
do_build=1

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

if [[ -z "$coqproject" ]]; then
  coqproject="$tool_root/_CoqProject"
fi

if [[ -z "$opam_env_dir" ]]; then
  opam_env_dir="$tool_root"
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
