#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT
cabal exec -- ghc -O2 -w -isrc test/v1/FullRuntimeRegression.hs src/X/term.c src/X/higher_machine.c -Isrc/X -odir "$tmp_dir" -hidir "$tmp_dir" -o "$tmp_dir/regression" > "$tmp_dir/build.log" 2>&1 || {
    cat "$tmp_dir/build.log"
    exit 1
}
python3 - "$tmp_dir/regression" <<'PY'
import subprocess
import sys

subprocess.run([sys.argv[1]], check=True, timeout=10)
PY
