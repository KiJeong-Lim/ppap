#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/extract-gofile-v.sh [options] path/to/gofile.v

Options:
  --tool-root=DIR       Private tool checkout root.
                        Default: PROJECT_A_TOOL_ROOT or the value injected by a/boot.sh
  --workdir=DIR         Project A work directory.
                        Default: PROJECT_A_WORKDIR or .project-a-gofile-extract
  --mod=TERM            Mod.t term to compile and extract.
                        Default: PROJECT_A_EXTRACT_MOD or Input.t
  --require=M1,M2       Extra Coq modules to Require Import before --mod.
                        Default: PROJECT_A_EXTRACT_REQUIRE
  --output=FILE         Extracted Haskell file name.
                        Default: PROJECT_A_EXTRACT_OUTPUT or ExtractedMain.hs
  --coqproject=FILE     _CoqProject file(s), comma-separated.
                        Default: PROJECT_A_COQPROJECTS or tool-root/_CoqProject
  --opam-env-dir=DIR    Directory where `opam env` should be evaluated.
                        Default: PROJECT_A_OPAM_ENV_DIR or tool-root
  --coqc=COQC           coqc command. Default: PROJECT_A_COQC or coqc
  --no-build            Skip `cabal build`.
  -h, --help            Show this help.

The input file is copied into the extraction harness as ProjectA.Input.
So a file that defines `Definition t : Mod.t := ...` can use the default
`--mod=Input.t`.
EOF
}

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
tool_root="${PROJECT_A_TOOL_ROOT:-/home/lim/Desktop/GoCris/go2c}"
workdir="${PROJECT_A_WORKDIR:-.project-a-gofile-extract}"
mod_term="${PROJECT_A_EXTRACT_MOD:-Input.t}"
requires="${PROJECT_A_EXTRACT_REQUIRE:-}"
output_file="${PROJECT_A_EXTRACT_OUTPUT:-ExtractedMain.hs}"
coqproject="${PROJECT_A_COQPROJECTS:-}"
opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-}"
coqc_command="${PROJECT_A_COQC:-}"
do_build=1
coq_file=""

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
    --tool-root=*)
      tool_root="${1#*=}"
      shift
      ;;
    --tool-root)
      tool_root="${2:?missing value for --tool-root}"
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
    --output=*)
      output_file="${1#*=}"
      shift
      ;;
    --output)
      output_file="${2:?missing value for --output}"
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
    --*)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      if [[ -n "$coq_file" ]]; then
        echo "error: only one gofile.v may be provided" >&2
        usage >&2
        exit 2
      fi
      coq_file="$1"
      shift
      ;;
  esac
done

if [[ -z "$coq_file" ]]; then
  echo "error: missing path/to/gofile.v" >&2
  usage >&2
  exit 2
fi

if [[ ! -f "$coq_file" ]]; then
  echo "error: input file does not exist: $coq_file" >&2
  exit 2
fi

coq_file="$(realpath "$coq_file")"

if [[ "$tool_root" == "/home/lim/Desktop/GoCris/go2c" ]]; then
  echo "error: this checkout has not been booted; run a/boot.sh or set PROJECT_A_TOOL_ROOT" >&2
  exit 2
fi

reject_whitespace "--tool-root" "$tool_root"
reject_whitespace "--workdir" "$workdir"
reject_whitespace "--mod" "$mod_term"
reject_whitespace "--require" "$requires"
reject_whitespace "--output" "$output_file"
reject_whitespace "--coqproject" "$coqproject"
reject_whitespace "--opam-env-dir" "$opam_env_dir"
reject_whitespace "--coqc" "$coqc_command"
reject_whitespace "gofile.v" "$coq_file"

cmd=(Project --mod-extract "--tool-root=$tool_root" "--workdir=$workdir" "--coq-file=$coq_file" "--mod=$mod_term" "--output=$output_file")

if [[ -n "$requires" ]]; then
  cmd+=("--require=$requires")
fi

if [[ -n "$coqproject" ]]; then
  cmd+=("--coqproject=$coqproject")
fi

if [[ -n "$opam_env_dir" ]]; then
  cmd+=("--opam-env-dir=$opam_env_dir")
fi

if [[ -n "$coqc_command" ]]; then
  cmd+=("--coqc=$coqc_command")
fi

cd "$repo_root"

if [[ "$do_build" -eq 1 ]]; then
  cabal build
fi

printf '%s\n\n' "${cmd[*]}" | cabal run -v0 ppap
