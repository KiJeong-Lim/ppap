#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/go-dir-diff.sh [options] DIR

Options:
  --workdir=DIR          Project A work directory.
                         Default: PROJECT_A_WORKDIR or .project-a-go-dir-work
  --translator=CMD       Command that reads gofile.go and writes generated Coq to stdout.
                         Default: PROJECT_A_TRANSLATOR
  --extract-mode=MODE    Extraction mode: mod or direct.
                         Default: PROJECT_A_EXTRACT_MODE or mod
  --tool-root=DIR        Private tool checkout root.
                         Default: PROJECT_A_TOOL_ROOT
  --mod=TERM             Mod.t term exposed by the generated Coq file.
                         Default: PROJECT_A_EXTRACT_MOD or Input.t
  --require=M1,M2        Extra Coq modules to Require Import before --mod.
                         Default: PROJECT_A_EXTRACT_REQUIRE
  --coqproject=FILE      _CoqProject file(s), comma-separated.
                         Default: PROJECT_A_COQPROJECTS
  --opam-env-dir=DIR     Directory where `opam env` should be evaluated.
                         Default: PROJECT_A_OPAM_ENV_DIR
  --coqc=COQC            coqc command.
                         Default: PROJECT_A_COQC or coqc
  --ghc-args=ARGS        Extra GHC args, comma-separated.
                         Default: PROJECT_A_GHC_ARGS
  --stdin=TEXT           Stdin passed to every tested Go program. No whitespace.
  --stdin-file=FILE      File whose contents are stdin for every tested Go program.
  --arg=ARG              Runtime argument passed to every tested Go program.
                         May be repeated. No whitespace.
  --env=KEY=VALUE        Runtime environment entry passed to every tested Go program.
                         May be repeated. No whitespace.
  --non-recursive        Only test .go files directly under DIR.
  --allow-non-pass       Exit 0 even if Project A reports non-PASS statuses.
  --no-build             Skip `cabal build`.
  -h, --help             Show this help.

The script runs Project A's go-file pipeline for every .go file under DIR.
Paths and Project A command arguments may not contain whitespace because ppap's
interactive command parser is whitespace-delimited.
EOF
}

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
go_dir=""
workdir="${PROJECT_A_WORKDIR:-.project-a-go-dir-work}"
translator="${PROJECT_A_TRANSLATOR:-}"
extract_mode="${PROJECT_A_EXTRACT_MODE:-mod}"
tool_root="${PROJECT_A_TOOL_ROOT:-}"
mod_term="${PROJECT_A_EXTRACT_MOD:-Input.t}"
requires="${PROJECT_A_EXTRACT_REQUIRE:-}"
coqproject="${PROJECT_A_COQPROJECTS:-}"
opam_env_dir="${PROJECT_A_OPAM_ENV_DIR:-}"
coqc_command="${PROJECT_A_COQC:-}"
ghc_args="${PROJECT_A_GHC_ARGS:-}"
stdin_text="${PROJECT_A_STDIN:-}"
stdin_file=""
recursive=1
fail_on_non_pass=1
do_build=1
runtime_args=()
runtime_env=()

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
    --non-recursive)
      recursive=0
      shift
      ;;
    --allow-non-pass)
      fail_on_non_pass=0
      shift
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
    --extract-mode=*)
      extract_mode="${1#*=}"
      shift
      ;;
    --extract-mode)
      extract_mode="${2:?missing value for --extract-mode}"
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
    --stdin=*)
      stdin_text="${1#*=}"
      shift
      ;;
    --stdin)
      stdin_text="${2:?missing value for --stdin}"
      shift 2
      ;;
    --stdin-file=*)
      stdin_file="${1#*=}"
      shift
      ;;
    --stdin-file)
      stdin_file="${2:?missing value for --stdin-file}"
      shift 2
      ;;
    --arg=*)
      runtime_args+=("${1#*=}")
      shift
      ;;
    --arg)
      runtime_args+=("${2:?missing value for --arg}")
      shift 2
      ;;
    --env=*)
      runtime_env+=("${1#*=}")
      shift
      ;;
    --env)
      runtime_env+=("${2:?missing value for --env}")
      shift 2
      ;;
    --*)
      echo "error: unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      if [[ -n "$go_dir" ]]; then
        echo "error: only one DIR may be provided" >&2
        usage >&2
        exit 2
      fi
      go_dir="$1"
      shift
      ;;
  esac
done

if [[ -z "$go_dir" ]]; then
  echo "error: missing DIR" >&2
  usage >&2
  exit 2
fi

if [[ ! -d "$go_dir" ]]; then
  echo "error: DIR does not exist or is not a directory: $go_dir" >&2
  exit 2
fi

if [[ -z "$translator" ]]; then
  echo "error: --translator=CMD or PROJECT_A_TRANSLATOR is required" >&2
  exit 2
fi

case "$extract_mode" in
  mod|direct)
    ;;
  *)
    echo "error: --extract-mode must be mod or direct: $extract_mode" >&2
    exit 2
    ;;
esac

reject_whitespace "DIR" "$go_dir"
reject_whitespace "--workdir" "$workdir"
reject_whitespace "--extract-mode" "$extract_mode"
reject_whitespace "--tool-root" "$tool_root"
reject_whitespace "--mod" "$mod_term"
reject_whitespace "--require" "$requires"
reject_whitespace "--coqproject" "$coqproject"
reject_whitespace "--opam-env-dir" "$opam_env_dir"
reject_whitespace "--coqc" "$coqc_command"
reject_whitespace "--ghc-args" "$ghc_args"
reject_whitespace "--stdin" "$stdin_text"
reject_whitespace "--stdin-file" "$stdin_file"

for value in "${runtime_args[@]}"; do
  reject_whitespace "--arg" "$value"
done

for value in "${runtime_env[@]}"; do
  reject_whitespace "--env" "$value"
done

if [[ -n "$stdin_file" && ! -f "$stdin_file" ]]; then
  echo "error: --stdin-file does not exist: $stdin_file" >&2
  exit 2
fi

go_dir_abs="$(cd "$go_dir" && pwd)"

if [[ "$recursive" -eq 1 ]]; then
  mapfile -d '' go_files < <(find "$go_dir_abs" -type f -name '*.go' -print0 | sort -z)
else
  mapfile -d '' go_files < <(find "$go_dir_abs" -maxdepth 1 -type f -name '*.go' -print0 | sort -z)
fi

if [[ "${#go_files[@]}" -eq 0 ]]; then
  echo "error: no .go files found under: $go_dir_abs" >&2
  exit 2
fi

for go_file in "${go_files[@]}"; do
  reject_whitespace ".go path" "$go_file"
done

cmd=(Project --go-files "--workdir=$workdir")

for go_file in "${go_files[@]}"; do
  cmd+=("--go-file=$go_file")
done

if [[ -n "$stdin_text" ]]; then
  cmd+=("--stdin=$stdin_text")
fi

if [[ -n "$stdin_file" ]]; then
  cmd+=("--stdin-file=$stdin_file")
fi

for value in "${runtime_args[@]}"; do
  cmd+=("--arg=$value")
done

for value in "${runtime_env[@]}"; do
  cmd+=("--env=$value")
done

env_args=(
  "PROJECT_A_TRANSLATOR=$translator"
  "PROJECT_A_EXTRACT_MODE=$extract_mode"
)

if [[ -n "$tool_root" ]]; then
  env_args+=("PROJECT_A_TOOL_ROOT=$tool_root")
fi

if [[ -n "$mod_term" ]]; then
  env_args+=("PROJECT_A_EXTRACT_MOD=$mod_term")
fi

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

mkdir -p "$workdir"
input_file="$(mktemp "$workdir/ppap-input.XXXXXX")"
output_file="$(mktemp "$workdir/ppap-output.XXXXXX")"
cleanup() {
  rm -f "$input_file"
}
trap cleanup EXIT

printf '%s\n\n' "${cmd[*]}" >"$input_file"

echo "Project A go-dir differential test"
echo "go-dir: $go_dir_abs"
echo "go-files: ${#go_files[@]}"
echo "workdir: $workdir"

env PPAP_COLOR="${PPAP_COLOR:-never}" "${env_args[@]}" cabal run -v0 ppap <"$input_file" | tee "$output_file"

status_count="$(grep -c '^status: ' "$output_file" || true)"
pass_count="$(grep -c '^status: PASS$' "$output_file" || true)"
non_pass_count="$((status_count - pass_count))"

echo "summary: total=$status_count pass=$pass_count non-pass=$non_pass_count"
echo "output-log: $output_file"

if [[ "$fail_on_non_pass" -eq 1 && "$non_pass_count" -gt 0 ]]; then
  exit 1
fi
