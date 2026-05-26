#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  a/randomgen.sh [options]

Options:
  --cases=N     Number of Go files to print.
                Default: PROJECT_A_RANDOMGEN_CASES or 10
  --seed=N      Initial generator seed.
                Default: PROJECT_A_RANDOMGEN_SEED or current Unix time
  --size=N      Generator size.
                Default: PROJECT_A_RANDOMGEN_SIZE or 6
  --no-build    Skip `cabal build`.
  -h, --help    Show this help.
EOF
}

cd "$(dirname "$0")/.."

cases="${PROJECT_A_RANDOMGEN_CASES:-10}"
seed="${PROJECT_A_RANDOMGEN_SEED:-$(date +%s)}"
size="${PROJECT_A_RANDOMGEN_SIZE:-6}"
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

if [[ "$do_build" -eq 1 ]]; then
  cabal build >/dev/null
fi

printf 'Project --print-go --cases=%s --seed=%s --size=%s\n\n' "$cases" "$seed" "$size" \
  | PPAP_COLOR=never cabal run -v0 ppap \
  | awk 'BEGIN { emitting = 0 } /^\/\/ randomgen case / { emitting = 1 } emitting { print }'
