#!/usr/bin/env bash
# test/smoke.sh — BETA conformance runner (HolBETA Chapter 10).
#
# Runs every test/**/*.hol through the `ppap` executable using its
# sibling *.input.txt as the REPL transcript, then diffs the captured
# output against the sibling *.expected.txt. Exits 0 iff every case
# matches byte-for-byte.
#
# Invocation:
#  ./test/smoke.sh          (runs from project root)
#  ./test/smoke.sh --update (rewrites successful *.expected.txt files.)
#  ./test/smoke.sh --update --allow-errors (also rewrites transcripts containing diagnostics.)

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR" || exit 2

UPDATE=0
ALLOW_ERROR_UPDATES=0
for arg in "$@"; do
    case "$arg" in
        --update) UPDATE=1 ;;
        --allow-errors) ALLOW_ERROR_UPDATES=1 ;;
        *)
            echo "smoke.sh: unknown argument: $arg"
            exit 2
            ;;
    esac
done

TMP_DIR="$(mktemp -d)" || exit 2
trap 'rm -rf -- "$TMP_DIR"' EXIT
PROJECT_ROOT="$(pwd -P)"

if command -v timeout >/dev/null 2>&1; then
    TIMEOUT_BIN=timeout
elif command -v gtimeout >/dev/null 2>&1; then
    TIMEOUT_BIN=gtimeout
else
    echo "smoke.sh: neither timeout nor gtimeout is available"
    exit 2
fi

# Diagnostics intentionally contain canonical absolute paths.  Keep byte-exact
# goldens portable across checkouts by normalizing only that canonical root;
# all other bytes (including whitespace and final newlines) remain significant.
normalize_root() {
    local input=$1
    local escaped
    # Escape every character that is special either to a basic regular
    # expression or to the chosen sed delimiter.  Treat the checkout path as
    # literal text; paths containing '.', '[', '*', '^', '$', or '\\' must not
    # broaden the replacement expression.
    escaped=$(printf '%s' "$PROJECT_ROOT" | sed 's/[][\\.^$*|]/\\&/g') || return 1
    sed "s|$escaped|<PROJECT_ROOT>|g" "$input"
}

if [ -n "${PPAP_BIN-}" ]; then
    if [ ! -x "$PPAP_BIN" ]; then
        echo "smoke.sh: PPAP_BIN is not executable: $PPAP_BIN"
        exit 2
    fi
else
    cabal build ppap >/dev/null 2>&1 || {
        echo "smoke.sh: cabal build ppap failed"
        exit 2
    }
    PPAP_BIN="$(cabal list-bin ppap 2>/dev/null)" || {
        echo "smoke.sh: could not locate the ppap executable"
        exit 2
    }
fi

CASES=()
while IFS= read -r hol; do
    CASES+=("$hol")
done < <(find test -name '*.hol' | sort)
if [ ${#CASES[@]} -eq 0 ]; then
    echo "smoke.sh: no test/**/*.hol cases found"
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
        echo "MISS   $hol  (no sibling .input.txt)"
        missing=$((missing + 1))
        continue
    fi

    actual="$TMP_DIR/actual.txt"
    "$TIMEOUT_BIN" 60 "$PPAP_BIN" <"$input" >"$actual" 2>&1
    actual_exit=$?

    if [ $UPDATE -eq 1 ]; then
        if [ $actual_exit -eq 0 ]; then
            if [ $ALLOW_ERROR_UPDATES -eq 0 ] && grep -Eq 'error: \[Hol(BETA|ALPHA2)-' "$actual"; then
                echo "REFUSE $hol  (diagnostic transcript; pass --allow-errors to approve it explicitly)"
                fail=$((fail + 1))
                failing_cases+=("$hol")
            else
                candidate="$TMP_DIR/expected-candidate.txt"
                if normalize_root "$actual" >"$candidate"; then
                    mv -- "$candidate" "$expected"
                    echo "UPDATE $hol"
                    pass=$((pass + 1))
                else
                    echo "FAIL   $hol  (could not normalize checkout path)"
                    fail=$((fail + 1))
                    failing_cases+=("$hol")
                fi
            fi
        else
            echo "FAIL   $hol  (exit=$actual_exit; expected output not updated)"
            fail=$((fail + 1))
            failing_cases+=("$hol")
        fi
        continue
    fi

    if [ ! -f "$expected" ]; then
        echo "MISS   $hol  (no sibling .expected.txt; run with --update to seed)"
        missing=$((missing + 1))
        continue
    fi

    actual_normalized="$TMP_DIR/actual-normalized.txt"
    expected_normalized="$TMP_DIR/expected-normalized.txt"
    if ! normalize_root "$actual" >"$actual_normalized" \
        || ! normalize_root "$expected" >"$expected_normalized"; then
        echo "FAIL   $hol  (could not normalize checkout path)"
        fail=$((fail + 1))
        failing_cases+=("$hol")
        continue
    fi
    if [ $actual_exit -eq 0 ] && cmp -s "$actual_normalized" "$expected_normalized"; then
        echo "PASS   $hol"
        pass=$((pass + 1))
    else
        echo "FAIL   $hol  (exit=$actual_exit)"
        diff -u "$expected_normalized" "$actual_normalized" | sed 's/^/      /'
        fail=$((fail + 1))
        failing_cases+=("$hol")
    fi
done

AUX_CASES=()
while IFS= read -r script; do
    AUX_CASES+=("$script")
done < <(find test -mindepth 2 -type f -name '*.sh' | sort)
for script in "${AUX_CASES[@]}"; do
    actual="$TMP_DIR/$(basename "$script").txt"
    if PPAP_BIN="$PPAP_BIN" "$TIMEOUT_BIN" 60 bash "$script" >"$actual" 2>&1; then
        echo "PASS   $script"
        pass=$((pass + 1))
    else
        actual_exit=$?
        echo "FAIL   $script  (exit=$actual_exit)"
        sed 's/^/      /' "$actual"
        fail=$((fail + 1))
        failing_cases+=("$script")
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
