#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

python3 - "$PPAP_BIN" <<'PY'
from difflib import unified_diff
from pathlib import Path
import re
import subprocess
import sys
import tempfile


binary = str(Path(sys.argv[1]).resolve())


def check(condition, message, output=""):
    if not condition:
        raise SystemExit(f"V1 dispatch regression: {message}\n{output}")


def run(entries):
    result = subprocess.run(
        [binary], input="\n".join(entries) + "\n", text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10,
    )
    check(result.returncode == 0, "process failed", result.stdout)
    check("error: [" not in result.stdout and "BETA compatibility:" not in result.stdout,
        "query failed or left the native runtimes", result.stdout)
    return result.stdout


def observable(output):
    lines = []
    screen = False
    for line in output.splitlines():
        if line.startswith(("ppap >>= exec (", "Hol> Compiling ")):
            continue
        if line == "--------------------------------":
            screen = not screen
        elif not screen:
            lines.append(line)
    check(not screen, "unterminated debugger inspection screen", output)
    return "\n".join(lines)


def equivalent(label, expected, actual):
    lhs, rhs = observable(expected), observable(actual)
    difference = "\n".join(unified_diff(
        lhs.splitlines(), rhs.splitlines(), fromfile="BETA", tofile="V1",
    ))
    check(lhs == rhs, f"{label} changed answers or search order", difference)


def bindings(output):
    return re.findall(r"> ([A-Z][A-Za-z0-9_]*) := (.+)\.\n", output)


def results(output):
    return re.findall(r"> (yes\.|no\.)\n", output)


def version(path):
    content = path.read_text()
    if content.startswith("BytecodeArtifact 1 "):
        return 1
    if content.startswith("FullArtifact 2 "):
        return 2
    raise SystemExit(f"V1 dispatch regression: unknown artifact format in {path}")


with tempfile.TemporaryDirectory(prefix="dispatch-", dir="test/v1") as temporary:
    directory = Path(temporary)
    source = directory / "program.hol"
    source.write_text(r"""kind color type.
type red color.
type blue color.
type green color.
type choice (color -> o).
choice red.
choice blue.
choice green.
type one (color -> o).
one red.
type last (color -> o).
last green.
type first (color -> o).
first X :- choice X, !.
type bind ((color -> o) -> o).
bind choice.
type arithmetic (nat -> o).
arithmetic X :- X is 2 * 3.
type chosen ((color -> o) -> color -> o).
chosen P X :- P = choice, P X.
""")
    colors = [("X", "red"), ("X", "blue"), ("X", "green")]
    # Conservative fallback remains valid when control flow does not prove
    # the predicate. Proven aliases must retain all original choice points.
    cases = [
        ("known predicate", "?- sigma P\\ P = choice, P X.", 3, colors, 1),
        ("reversed equality", "?- sigma P\\ choice = P, P X.", 3, colors, 1),
        ("ordinary clause body", "?- chosen choice X.", 3, colors, 1),
        ("shadowed sigma", "?- sigma P\\ P = choice, (sigma P\\ P = one, P X), P Y.", 3,
            [("X", "red"), ("Y", "red"), ("X", "red"), ("Y", "blue"), ("X", "red"), ("Y", "green")], 1),
        ("nested outer reference", "?- sigma P\\ P = choice, sigma Q\\ Q = one, P X, Q Y.", 3,
            [("X", "red"), ("Y", "red"), ("X", "blue"), ("Y", "red"), ("X", "green"), ("Y", "red")], 1),
        ("wildcard before sigma", "?- choice _, sigma P\\ P = one, P X.", 3,
            [("X", "red")] * 3, 1),
        ("nested data binder", "?- sigma X\\ X = red, sigma P\\ P = choice, P X, Y = X.", 1,
            [("Y", "red")], 1),
        ("both branches agree", "?- sigma P\\ (P = choice; P = choice), P X.", 6, colors * 2, 1),
        ("branch-local calls", "?- sigma P\\ (P = one, P X; P = last, P X).", 2,
            [("X", "red"), ("X", "green")], 1),
        ("branch-dependent alias", "?- sigma P\\ (P = one; P = last), P X.", 2,
            [("X", "red"), ("X", "green")], None),
        ("failed branch rollback", "?- sigma P\\ (P = one, fail; P = choice), P X.", 3, colors, None),
        ("inconsistent alias", "?- sigma P\\ P = choice, P = one, P X.", 0, [], None),
        ("query cut", "?- sigma P\\ P = choice, P X, !.", 1, [("X", "red")], 1),
        ("callee cut", "?- sigma P\\ P = first, choice X, P Y.", 3,
            [("X", "red"), ("Y", "red"), ("X", "blue"), ("Y", "red"), ("X", "green"), ("Y", "red")], 1),
        ("observable predicate alias", "?- P = choice, P X.", 3,
            [("P", "choice"), ("X", "red"), ("P", "choice"), ("X", "blue"), ("P", "choice"), ("X", "green")], 1),
        ("predicate supplied by a call", "?- sigma P\\ bind P, P X.", 3, colors, None),
        ("prior call constrains alias", "?- sigma P\\ bind P, P = one, P X.", 0, [], None),
        ("reachable arithmetic", "?- sigma P\\ P = arithmetic, P X.", 1, [("X", "6")], 2),
        ("dynamic hypothesis", "?- pi p\\ p => p.", 0, [], 2),
        ("higher-order lambda", "?- pi x\\ F x = x.", 1, [("F", "x\\ x")], 2),
    ]
    saved = None
    for index, (label, query, count, expected_bindings, expected_version) in enumerate(cases):
        entries = [str(source), query, *(["y"] * count), ":q"]
        beta = run(["Hol --test", *entries])
        expected_final = "yes." if label == "dynamic hypothesis" else "no."
        check(bindings(beta) == expected_bindings and results(beta) == [expected_final],
            f"invalid BETA reference for {label}", beta)
        artifact = directory / f"query-{index}.hbc"
        native = run([f"V1 --test --strict --emit-bytecode={artifact}", *entries])
        equivalent(label, beta, native)
        check(artifact.exists(), f"{label} did not emit bytecode", native)
        if expected_version is not None:
            check(version(artifact) == expected_version,
                f"{label} selected bytecode version {version(artifact)}, expected {expected_version}", native)
        if index == 0:
            saved = artifact

    core = cases[0][1]
    entries = [str(source), core, "y", "y", "y", ":q"]
    equivalent("Hol --v1 dispatch", run(["V1 --test --strict", *entries]),
        run(["Hol --v1 --test --strict", *entries]))
    dumped = run(["V1 --test --strict --dump-bytecode", *entries])
    check("HOL V1 bytecode version 1" in dumped and "HOL V1 bytecode version 2" not in dumped,
        "dump did not expose the selected first-order program", dumped)
    check(bindings(dumped) == colors and results(dumped) == ["no."],
        "dump changed the specialized answer sequence", dumped)

    forced_artifacts = []
    for index, query in enumerate([core, "?- choice X."]):
        artifact = directory / f"forced-{index}.hbc"
        entries = [str(source), query, "y", "y", "y", ":q"]
        forced = run([f"V1 --test --strict --general --emit-bytecode={artifact}", *entries])
        equivalent("explicit general engine", run(["Hol --test", *entries]), forced)
        check(version(artifact) == 2 and bindings(forced) == colors,
            "--general did not retain the full native engine", forced)
        forced_artifacts.append(artifact)
    forced_dump = run(["Hol --v1 --test --strict --general --dump-bytecode",
        str(source), core, "y", "y", "y", ":q"])
    check("HOL V1 bytecode version 2" in forced_dump and "HOL V1 bytecode version 1" not in forced_dump,
        "general dispatcher alias did not retain full bytecode", forced_dump)
    check(bindings(forced_dump) == colors and results(forced_dump) == ["no."],
        "general dump changed the answer sequence", forced_dump)

    reloaded_artifact = directory / "reloaded.hbc"
    reload_entries = [str(source), core, "y", "y", "y", ":reload", "?- choice X.", "y", "y", "y", ":q"]
    reloaded = run([f"V1 --test --strict --general --emit-bytecode={reloaded_artifact}", *reload_entries])
    equivalent("reload retains forced general engine", run(["Hol --test", *reload_entries]), reloaded)
    check(version(reloaded_artifact) == 2 and bindings(reloaded) == colors * 2,
        "reload lost explicit general engine selection", reloaded)

    debug_artifact = directory / "debug.hbc"
    debug_entries = [str(source), ":d", core, ":d", "y", "y", "y", ":q"]
    debug_beta = run(["Hol --test", *debug_entries])
    debug_native = run([f"V1 --test --strict --emit-bytecode={debug_artifact}", *debug_entries])
    equivalent("debugging retains the full engine", debug_beta, debug_native)
    check(version(debug_artifact) == 2 and bindings(debug_native) == colors,
        "debugging incorrectly selected the first-order engine", debug_native)

    source.unlink()
    for artifact in [saved, *forced_artifacts, reloaded_artifact]:
        replay = run([f"V1 --test --run-bytecode={artifact}"])
        check(bindings(replay) == colors and results(replay) == ["no."]
            and replay.count("HolV1> Answer ") == 3,
            "selected artifact changed answers after source removal", replay)

print("V1 dispatch: alias specialization, branch/scope/cut semantics, forced general mode, reload, debugger and artifact replay passed")
PY
