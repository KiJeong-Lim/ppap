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
grep -F 'hol >>= quit' "$ALPHA1_TEST_DIR/debugging.txt" >/dev/null
if grep -F 'hol> yes.' "$ALPHA1_TEST_DIR/debugging.txt" >/dev/null; then
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
printf 'type p o.\np :- debug "x".\n' >"$ALPHA1_TEST_DIR/dbg.hol"
printf 'ALPHA1\n%s/dbg\n?- p.\n\n?- true.\n:q\n' "$ALPHA1_TEST_DIR" | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/debug_scope.txt" 2>&1
if [ "$(grep -c 'Press the enter key' "$ALPHA1_TEST_DIR/debug_scope.txt")" -ne 1 ]; then
    echo 'ALPHA1 debug outlived its query'
    exit 1
fi
grep -F 'dbg> yes.' "$ALPHA1_TEST_DIR/debug_scope.txt" >/dev/null
printf 'ALPHA1\ntest/alpha1/legacy\n?- add _ 2 X.\nn\n\n?- add _X 2 Y.\nn\n:q\n' | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/wildcard.txt" 2>&1
grep -F 'X := 2.' "$ALPHA1_TEST_DIR/wildcard.txt" >/dev/null
grep -F '_X := 0.' "$ALPHA1_TEST_DIR/wildcard.txt" >/dev/null
grep -F 'Y := 2.' "$ALPHA1_TEST_DIR/wildcard.txt" >/dev/null
if grep -F 'wild' "$ALPHA1_TEST_DIR/wildcard.txt" >/dev/null; then
    echo 'ALPHA1 wildcard leaked into an answer'
    exit 1
fi
printf 'ALPHA1\nfoo.txt\ntest/alpha1/legacy\n?- true.\n:q\n' | "$PPAP_EXECUTABLE" >"$ALPHA1_TEST_DIR/extension.txt" 2>&1
grep -F "loading-error: \`.txt'" "$ALPHA1_TEST_DIR/extension.txt" >/dev/null
grep -F 'test.alpha1.legacy> yes.' "$ALPHA1_TEST_DIR/extension.txt" >/dev/null
echo 'ALPHA1 debugger scope, wildcard, blank-line and extension regressions passed'
