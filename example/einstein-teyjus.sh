#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

BUILD_OPTIONS=(
    --enable-optimization=2
    "--ghc-options=-O2 -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fspecialise-aggressively"
)
cabal build exe:ppap "${BUILD_OPTIONS[@]}"
PPAP_EXECUTABLE=$(cabal list-bin exe:ppap "${BUILD_OPTIONS[@]}")
python3 example/teyjus/benchmark.py --ppap-bin "$PPAP_EXECUTABLE" "$@"
