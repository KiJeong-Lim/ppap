#!/usr/bin/env bash
# Test/smoke.sh — BETA1 smoke runner (spec section 4.6.2).
#
# Runs every Test/**/*.hol through the `ppap` executable using its
# sibling *.input.txt as the REPL transcript, then diffs the captured
# output against the sibling *.expected.txt. Exits 0 iff every case
# matches byte-for-byte.
#
# Invocation:  ./Test/smoke.sh              (runs from project root)
#              ./Test/smoke.sh --update     (rewrites *.expected.txt
#                                            instead of diffing — for
#                                            authoring new cases.)

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR" || exit 2

UPDATE=0
if [ "${1-}" = "--update" ]; then
    UPDATE=1
fi

cabal build ppap >/dev/null 2>&1 || {
    echo "smoke: cabal build ppap failed"
    exit 2
}

mapfile -t CASES < <(find Test -name '*.hol' | sort)
if [ ${#CASES[@]} -eq 0 ]; then
    echo "smoke: no Test/**/*.hol cases found"
    exit 2
fi

pass=0
fail=0
missing=0
failing_cases=()

for hol in "${CASES[@]}"; do
    base="${hol%.hol}"
    input="$base.input.txt"
    expected="$base.expected.txt"

    if [ ! -f "$input" ]; then
        echo "MISS  $hol  (no sibling .input.txt)"
        missing=$((missing + 1))
        continue
    fi

    actual="$(cat "$input" | timeout 60 cabal run -v0 ppap 2>&1)"
    actual_exit=$?

    if [ $UPDATE -eq 1 ]; then
        printf '%s\n' "$actual" > "$expected"
        echo "UPDATE $hol"
        continue
    fi

    if [ ! -f "$expected" ]; then
        echo "MISS  $hol  (no sibling .expected.txt; run with --update to seed)"
        missing=$((missing + 1))
        continue
    fi

    expected_content="$(cat "$expected")"
    if [ "$actual" = "$expected_content" ]; then
        echo "PASS  $hol"
        pass=$((pass + 1))
    else
        echo "FAIL  $hol  (exit=$actual_exit)"
        diff -u <(printf '%s\n' "$expected_content") <(printf '%s\n' "$actual") | sed 's/^/      /'
        fail=$((fail + 1))
        failing_cases+=("$hol")
    fi
done

echo
echo "smoke: $pass passed, $fail failed, $missing missing"
if [ $fail -gt 0 ]; then
    exit 1
fi
if [ $missing -gt 0 ]; then
    exit 2
fi
exit 0
