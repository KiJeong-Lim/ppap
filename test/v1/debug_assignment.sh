#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

python3 - "$PPAP_BIN" <<'PY'
from difflib import unified_diff
from pathlib import Path
import subprocess
import sys


binary = str(Path(sys.argv[1]).resolve())


def observable(output):
    lines = []
    screen = False
    for line in output.splitlines():
        if line.startswith(("ppap >>= exec (", "Hol> Compiling ")):
            continue
        # C continuations and BETA's materialized Stack have different internal
        # identities. Keep every command result, diagnostic and answer outside
        # the inspection screens.
        if line == "--------------------------------":
            screen = not screen
        elif not screen:
            lines.append(line)
    if screen:
        raise SystemExit("V1 debugger assignment: unterminated debugger screen")
    return "\n".join(lines)


def run(backend, entries):
    result = subprocess.run(
        [binary], input="\n".join([backend, *entries]) + "\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10,
    )
    if result.returncode or "BETA compatibility:" in result.stdout:
        raise SystemExit(f"V1 debugger assignment: {backend} failed\n{result.stdout}")
    return observable(result.stdout)


def check(label, entries, required):
    beta = run("Hol --test", entries)
    native = run("V1 --test --strict", entries)
    if any(fragment not in beta for fragment in required):
        raise SystemExit(f"V1 debugger assignment: invalid BETA reference for {label}\n{beta}")
    if beta != native:
        difference = "\n".join(unified_diff(
            beta.splitlines(), native.splitlines(), fromfile="BETA", tofile="V1",
        ))
        raise SystemExit(f"V1 debugger assignment: {label}\n{difference}")


# Presburger closures are opaque to ordinary unification; explicit, checked
# debugger replacement can still assign one to a proposition variable.
check("opaque ordinary unification", [
    "", '?- sigma P\\ P = presburger "1 = 1", P.', ":q",
], ["Hol> no."])
check("opaque direct assignment", [
    "", ":d", "?- P.", ':assign ?P := presburger "1 = 1".', ":d", "n", ":q",
], [
    'Hol> *** :assign: P := presburger "1 = 1".',
    'Hol> P := presburger "1 = 1".', "Hol> yes.",
])

# Existing fixtures also verify that rejected assignment is transactional: the
# original query continues to produce its answer after the diagnostic.
for fixture, diagnostic, answer in [
    ("assign_fail", "occurs check failed for 'X'", "X := 0."),
    ("assign_fail_scope", "scope violation for 'X'", "X := E_1."),
    ("assign_fail_typing", "The assignment is inconsistent with the active debugger variable types.", "X := 0."),
]:
    entries = Path(f"test/debug/{fixture}.input.txt").read_text().splitlines()[1:]
    check(fixture, entries, ["error: [HolBETA-AssignError]", diagnostic, answer, "> yes."])

print("V1 debugger assignment: opaque replacement and transactional occurs/scope/type rejection matched BETA")
PY
