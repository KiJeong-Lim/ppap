#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

BUILD_OPTIONS=(
    --enable-optimization=2
    "--ghc-options=-O2 -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fspecialise-aggressively"
)
cabal build exe:ppap "${BUILD_OPTIONS[@]}"
PPAP_EXECUTABLE=$(cabal list-bin exe:ppap "${BUILD_OPTIONS[@]}")

# Strict mode requires the V1 bytecode VM for the complete answer search.
printf '%s\n' 'V1 --test --strict' 'example/einstein.hol' '?- answer Houses.' 'y' ':q' | "$PPAP_EXECUTABLE"
