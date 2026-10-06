#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/../.."
cabal exec -- runghc -isrc test/alpha1/LegacyRegression.hs
PPAP_EXECUTABLE=${PPAP_BIN:-$(cabal list-bin ppap)}
ALPHA1_TEST_DIR=$(mktemp -d)
trap 'rm -rf -- "$ALPHA1_TEST_DIR"' EXIT
printf 'ALPHA1\n%s/missing\ntest/alpha1/legacy\n?- true.\n:q\n' "$ALPHA1_TEST_DIR" | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/loading.txt" 2>&1
grep -F "loading-error: couldn't read" "$ALPHA1_TEST_DIR/loading.txt" >/dev/null
grep -F 'test.alpha1.legacy> yes.' "$ALPHA1_TEST_DIR/loading.txt" >/dev/null
printf 'ALPHA1\n\n:d\n?- true.\n:q\n' | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/debugging.txt" 2>&1
grep -F 'Aladdin >>= quit' "$ALPHA1_TEST_DIR/debugging.txt" >/dev/null
if grep -F 'Aladdin> yes.' "$ALPHA1_TEST_DIR/debugging.txt" >/dev/null; then
    echo 'ALPHA1 debugger continued after :q'
    exit 1
fi
printf 'ALPHA1\n\n?- X = 3.\n' | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/eof.txt" 2>&1
grep -F 'X := 3.' "$ALPHA1_TEST_DIR/eof.txt" >/dev/null
if grep -E 'end of file|Prelude.read|Non-exhaustive' "$ALPHA1_TEST_DIR/eof.txt" >/dev/null; then
    cat "$ALPHA1_TEST_DIR/eof.txt"
    exit 1
fi
echo 'ALPHA1 loading/debugger/EOF regressions passed'
printf 'ALPHA1\n\n?- X is Y + 1.\n?- X is 7 / 2.\n?- X is 1 // 0.\n?- X is 7 // 2.\nn\n:q\n' | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/arithmetic.txt" 2>&1
grep -F 'instantiation_error' "$ALPHA1_TEST_DIR/arithmetic.txt" >/dev/null
grep -F 'domain_error(nat' "$ALPHA1_TEST_DIR/arithmetic.txt" >/dev/null
grep -F 'evaluation_error(zero_divisor)' "$ALPHA1_TEST_DIR/arithmetic.txt" >/dev/null
grep -F 'X := 3.' "$ALPHA1_TEST_DIR/arithmetic.txt" >/dev/null
if grep -E 'Non-exhaustive|Prelude.read' "$ALPHA1_TEST_DIR/arithmetic.txt" >/dev/null; then
    cat "$ALPHA1_TEST_DIR/arithmetic.txt"
    exit 1
fi
echo 'ALPHA1 arithmetic errors and REPL recovery passed'
