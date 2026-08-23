#!/usr/bin/env bash
set -eu

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [ -z "${PPAP_BIN-}" ]; then
    PPAP_BIN="$(cd "$ROOT_DIR" && cabal list-bin ppap)"
fi
OUTSIDE_DIR="$(mktemp -d)"
INSIDE_DIR="$(mktemp -d "$ROOT_DIR/.audit_module_outside.XXXXXX")"
trap 'rm -rf -- "$OUTSIDE_DIR" "$INSIDE_DIR"' EXIT

printf 'type outside (nat -> o).\noutside 1.\n' >"$OUTSIDE_DIR/outside.hol"

direct_output="$(cd "$ROOT_DIR" && printf 'Hol --test\n%s\n:q\n' "$OUTSIDE_DIR/outside.hol" | "$PPAP_BIN" 2>&1)"
printf '%s\n' "$direct_output" | grep -F 'is outside the project root' >/dev/null

ln -s "$OUTSIDE_DIR/outside.hol" "$INSIDE_DIR/escape.hol"
printf 'import escape.\n' >"$INSIDE_DIR/main.hol"
relative_main="${INSIDE_DIR#"$ROOT_DIR/"}/main.hol"
import_output="$(cd "$ROOT_DIR" && printf 'Hol --test\n%s\n:q\n' "$relative_main" | "$PPAP_BIN" 2>&1)"
printf '%s\n' "$import_output" | grep -F 'is outside the project root' >/dev/null

printf 'outside-root regression: ok\n'
