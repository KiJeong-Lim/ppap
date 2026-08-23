#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [ -z "${PPAP_BIN-}" ]; then
    PPAP_BIN="$(cd "$ROOT_DIR" && cabal list-bin ppap)"
fi

SCRATCH_DIR="$(mktemp -d "$ROOT_DIR/.audit_reload_atomic.XXXXXX")"
INPUT_FIFO="$SCRATCH_DIR/input.fifo"
OUTPUT_FILE="$SCRATCH_DIR/output.txt"
MODULE_FILE="$SCRATCH_DIR/main.hol"
RELATIVE_MODULE="${MODULE_FILE#"$ROOT_DIR/"}"

mkfifo "$INPUT_FIFO"
printf 'type survives o.\nsurvives.\n' >"$MODULE_FILE"

"$PPAP_BIN" <"$INPUT_FIFO" >"$OUTPUT_FILE" 2>&1 &
PPAP_PID=$!
trap 'kill "$PPAP_PID" 2>/dev/null || true; wait "$PPAP_PID" 2>/dev/null || true; rm -rf -- "$SCRATCH_DIR"' EXIT
exec 3>"$INPUT_FIFO"

wait_for_output() {
    local needle=$1
    local attempt
    for attempt in $(seq 1 200); do
        if grep -F "$needle" "$OUTPUT_FILE" >/dev/null 2>&1; then
            return 0
        fi
        if ! kill -0 "$PPAP_PID" 2>/dev/null; then
            printf 'reload-atomic regression: ppap exited while waiting for %s\n' "$needle"
            sed 's/^/  /' "$OUTPUT_FILE"
            return 1
        fi
        sleep 0.05
    done
    printf 'reload-atomic regression: timed out waiting for %s\n' "$needle"
    sed 's/^/  /' "$OUTPUT_FILE"
    return 1
}

printf 'Hol --test\n%s\n:d\n' "$RELATIVE_MODULE" >&3
wait_for_output 'Debugging mode on.'

# Make the requested main file invalid only after its first generation is
# active, then request a reload through the real REPL path.
printf 'type survives o' >"$MODULE_FILE"
printf ':reload\n' >&3
wait_for_output '[HolBETA-ParseError]'

# The second toggle must see the old `on' state, and the old fact must still be
# queryable.  A failed reload that falls back to a blank/fresh REPL fails both.
printf ':d\n?- survives.\n:q\n' >&3
exec 3>&-
wait "$PPAP_PID"

grep -F 'Debugging mode off.' "$OUTPUT_FILE" >/dev/null
grep -F 'yes.' "$OUTPUT_FILE" >/dev/null
if grep -F 'Ok, no module loaded.' "$OUTPUT_FILE" >/dev/null; then
    printf 'reload-atomic regression: failed reload discarded the active module\n'
    sed 's/^/  /' "$OUTPUT_FILE"
    exit 1
fi

printf 'failed-reload atomicity regression: ok\n'
