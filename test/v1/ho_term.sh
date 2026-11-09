#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
hol_v1_term_tmp=$(mktemp -d)
trap 'rm -rf -- "$hol_v1_term_tmp"' EXIT
"${CC:-cc}" -std=c11 -Wall -Wextra -Wpedantic -Werror -g -O1 \
    -fsanitize=address,undefined -fno-omit-frame-pointer \
    -Isrc/X src/X/term.c src/X/term_test.c -Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc -o "$hol_v1_term_tmp/term_test"
ASAN_OPTIONS=detect_leaks=1 "$hol_v1_term_tmp/term_test"
cabal exec -- runghc -isrc test/v1/HigherOrderDifferential.hs > "$hol_v1_term_tmp/reference.txt"
"${CC:-cc}" -std=c11 -Wall -Wextra -Wpedantic -Werror -O1 \
    -Isrc/X src/X/term.c src/X/term_compare.c -o "$hol_v1_term_tmp/compare"
python3 test/v1/ho_compare.py "$hol_v1_term_tmp/compare" "$hol_v1_term_tmp/reference.txt"
