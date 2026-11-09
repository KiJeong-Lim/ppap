#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
hol_v1_native_tmp=$(mktemp -d)
trap 'rm -rf -- "$hol_v1_native_tmp"' EXIT

python3 test/v1/native_fixtures.py "$hol_v1_native_tmp/machine_test_fixtures.h"
"${CC:-cc}" -std=c11 -Wall -Wextra -Wpedantic -Werror -g -O1 \
    -fsanitize=address,undefined -fno-omit-frame-pointer \
    -Isrc/X -I"$hol_v1_native_tmp" src/X/machine.c src/X/machine_test.c \
    -Wl,--wrap=calloc,--wrap=realloc -o "$hol_v1_native_tmp/machine_test"
ASAN_OPTIONS=detect_leaks=1:allocator_may_return_null=1 "$hol_v1_native_tmp/machine_test"
