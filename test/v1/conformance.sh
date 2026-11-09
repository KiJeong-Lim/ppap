#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"
python3 - "$PPAP_BIN" <<'PY'
from pathlib import Path
import difflib
import re
import subprocess
import sys

root = Path.cwd()
binary = str(Path(sys.argv[1]).resolve())

def observable(text):
    lines = []
    screen = False
    for line in text.replace(str(root), "<PROJECT_ROOT>").splitlines():
        if line.startswith(("ppap >>= exec (", "Hol> Compiling ")):
            continue
        # Native continuations/choice points and identity numbers differ from
        # BETA's materialized Stack. Commands, diagnostics and answer displays
        # outside these inspection screens must still match exactly.
        if line == "--------------------------------":
            screen = not screen
            continue
        if not screen:
            lines.append(line)
    if screen:
        raise SystemExit("unterminated debugger screen")
    return "\n".join(lines)

count = 0
for path in sorted(Path("test").rglob("*.input.txt")):
    lines = path.read_text().splitlines()
    if not lines or not re.fullmatch(r"Hol(?: --(?:test|pretty))?", lines[0]):
        continue
    expected = path.with_name(path.name.replace(".input.txt", ".expected.txt"))
    if not expected.exists():
        continue
    lines[0] = "V1 --test --strict"
    result = subprocess.run([binary], input="\n".join(lines) + "\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10)
    if result.returncode or "BETA compatibility:" in result.stdout:
        raise SystemExit(f"native conformance failed: {path}\n{result.stdout}")
    before = observable(expected.read_text())
    after = observable(result.stdout)
    if before != after:
        difference = "\n".join(difflib.unified_diff(before.splitlines(),
            after.splitlines(), fromfile="BETA", tofile="V1"))
        raise SystemExit(f"native conformance failed: {path}\n{difference}")
    count += 1
if count < 134:
    raise SystemExit(f"incomplete native conformance corpus: {count}")
print(f"V1 native conformance: {count} BETA transcripts matched answers, constraints, diagnostics and interactive commands")
PY
