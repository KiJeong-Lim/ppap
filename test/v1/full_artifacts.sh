#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

python3 - "$PPAP_BIN" <<'PY'
from pathlib import Path
import re
import subprocess
import sys
import tempfile


binary = str(Path(sys.argv[1]).resolve())


def run(entries, success=True):
    result = subprocess.run(
        [binary], input="\n".join(entries) + "\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10,
    )
    if (result.returncode == 0) != success:
        raise AssertionError(result.stdout)
    if success and ("error: [" in result.stdout or "BETA compatibility:" in result.stdout):
        raise AssertionError(result.stdout)
    return result.stdout


def bindings(output):
    return re.findall(r"> ([A-Z][A-Za-z0-9_]*) := (.+)\.\n", output)


with tempfile.TemporaryDirectory(prefix="v1-artifact-", dir="test/v1") as directory:
    root = Path(directory)
    source = root / "program.hol"
    source.write_text("""kind item type.
type a item.
type b item.
type pick (item -> o).
pick a.
pick b.
""")
    cases = [
        ("lambda", "?- pi x\\ F x = x.", ["y"], []),
        ("call", "?- sigma F\\ F = pick, F X.", ["y", "y"], [("X", "a"), ("X", "b")]),
        ("arithmetic", "?- sigma P\\ P = (X is 7), P.", ["y"], [("X", "7")]),
        ("quantifiers", '?- pi C\\ sigma X\\ presburger "X = C".', [], []),
        ("opaque", '?- sigma P\\ P = presburger "1 = 1", P.', [], []),
    ]
    saved = []
    for name, query, replies, expected in cases:
        artifact = root / (name + ".hbc")
        output = run([
            f"V1 --test --strict --general --emit-bytecode={artifact}", str(source),
            query, *replies, ":q",
        ])
        assert artifact.read_text().startswith("FullArtifact 2 "), output
        if name != "lambda":
            assert bindings(output) == expected, output
        saved.append((name, artifact, bindings(output)))

    source.unlink()
    for name, artifact, expected in saved:
        output = run([f"V1 --test --run-bytecode={artifact}"])
        assert "Hol =<<" not in output and "Compiling " not in output, output
        assert bindings(output) == expected, output
        if name == "quantifiers":
            assert "HolV1> yes." in output and "remaining constraints" not in output, output
        if name == "opaque":
            assert "HolV1> no." in output and "HolV1> Answer" not in output, output
        if name == "lambda":
            assert expected and expected[0][0] == "F" and "\\" in expected[0][1], output

    broken = root / "invalid.hbc"
    broken.write_text(saved[0][1].read_text().replace("FullArtifact 2 ", "FullArtifact 99 ", 1))
    rejected = run([f"V1 --test --run-bytecode={broken}"], success=False)
    assert "[HolV1-BytecodeError]" in rejected and "unsupported full HOL V1 artifact version" in rejected, rejected

print("V1 full artifacts: source-independent higher-order search, arithmetic, quantified answer projection and validation passed")
PY
