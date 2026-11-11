#!/usr/bin/env bash
# test/lol/host.sh — the Haskell host of LoL against lol/hol/kernel.hol.
#
# Builds test/lol/HostRegression.hs against src/ and runs it from the project
# root: Core <-> Hol terms, declarations through ground runs, and the ground-run
# protocol of doc/LoLALPHA1.txt, 5.3.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT
cabal exec -- ghc -O1 -w -isrc test/lol/HostRegression.hs src/X/term.c src/X/higher_machine.c -Isrc/X -odir "$tmp_dir" -hidir "$tmp_dir" -o "$tmp_dir/regression" > "$tmp_dir/build.log" 2>&1 || {
    cat "$tmp_dir/build.log"
    exit 1
}
python3 - "$tmp_dir/regression" <<'PY'
import resource
import subprocess
import sys

def limit():
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024 ** 3, 3 * 1024 ** 3))

subprocess.run([sys.argv[1]], check=True, timeout=40, preexec_fn=limit)
PY
