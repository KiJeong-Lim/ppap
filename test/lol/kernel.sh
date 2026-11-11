#!/usr/bin/env bash
# test/lol/kernel.sh — kernel-level tests of LoL (doc/LoLALPHA1.txt, Chapter 9).
#
# Runs the Hol modules under test/lol/kernel and test/lol/paradox against
# lol/hol/kernel.hol, on the Hol BETA interpreter and on the V1 general engine.
#
# Invocation:
#  ./test/lol/kernel.sh                  (the suite on both engines)
#  ./test/lol/kernel.sh --engine v1      (one engine: beta or v1)
#  ./test/lol/kernel.sh --mutants        (the mutation files, on v1)
#  ./test/lol/kernel.sh FILE...          (the given modules)
#  ./test/lol/kernel.sh --mutants FILE...  (the given mutation files)

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$ROOT_DIR" || exit 2

if [ -z "${PPAP_BIN-}" ]; then
    cabal build ppap >/dev/null 2>&1 || {
        echo "kernel.sh: cabal build ppap failed"
        exit 2
    }
    PPAP_BIN="$(cabal list-bin ppap 2>/dev/null)" || {
        echo "kernel.sh: could not locate the ppap executable"
        exit 2
    }
fi
export PPAP_BIN

exec python3 "$SCRIPT_DIR/kernel.py" "$@"
