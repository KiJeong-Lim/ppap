#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${PPAP_BIN:?smoke runner must provide PPAP_BIN}"

tmp_dir=$(mktemp -d "$PWD/test/v1/tmp.XXXXXX")
trap 'rm -rf -- "$tmp_dir"' EXIT

python3 - "$PPAP_BIN" "$tmp_dir" <<'PY'
from difflib import unified_diff
from pathlib import Path
import re
import subprocess
import sys


binary = str(Path(sys.argv[1]).resolve())
directory = Path(sys.argv[2])
source = directory / "native.hol"
source.write_text("""kind color type.
type red color.
type blue color.
type green color.
kind tree type.
type leaf tree.
type branch (tree -> tree).

type choice (color -> o).
choice red.
choice blue.
choice green.

type member (A -> list A -> o).
member X (X :: _).
member X (_ :: Rest) :- member X Rest.

type first (color -> o).
first X :- choice X, !.
type failedcut (color -> o).
failedcut X :- choice X, !, fail.
failedcut green.
type inner o.
inner :- !, fail.
type outer (color -> o).
outer red :- inner.
outer blue.
type aftercut (color -> o).
aftercut X :- !, (X = red; X = blue).
""")
module_path = str(source.relative_to(Path.cwd()))


def check(condition, message, output=""):
    if not condition:
        raise SystemExit(f"V1 CLI regression: {message}\n{output}")


def run(command, entries, module=module_path):
    transcript = "\n".join([command, module, *entries, ":q", ""])
    result = subprocess.run(
        [binary], input=transcript, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=8,
    )
    check(result.returncode == 0, f"{command} exited {result.returncode}", result.stdout)
    return result.stdout


def normalized(output, compatibility=False):
    # The dispatcher and compilation banners identify the selected backend.
    # Preserve every prompt, answer, error and search-exhaustion line.
    return "\n".join(
        line for line in output.splitlines()
        if not line.startswith("ppap >>= exec (")
        and not line.startswith("Hol> Compiling ")
        and not (compatibility and line.startswith("HolV1> BETA compatibility: "))
    )


def equivalent(label, expected, actual, compatibility=False):
    lhs = normalized(expected)
    rhs = normalized(actual, compatibility)
    difference = "\n".join(unified_diff(
        lhs.splitlines(), rhs.splitlines(), fromfile="BETA", tofile="V1",
    ))
    check(lhs == rhs, f"{label} changed the observable answer/search transcript", difference)


def bindings(output):
    return re.findall(r"> ([A-Z][A-Za-z0-9_]*) := (.+)\.\n", output)


def results(output):
    return re.findall(r"> (yes\.|no\.)\n", output)


cases = [
    ("clause order", "?- choice X.", 3,
        [("X", "red"), ("X", "blue"), ("X", "green")], "no."),
    ("recursive clauses", "?- member X [red, blue, green].", 3,
        [("X", "red"), ("X", "blue"), ("X", "green")], "no."),
    ("failed branch rolls bindings back", "?- (X = red, fail); X = blue.", 1,
        [("X", "blue")], "no."),
    ("cut commits the predicate activation", "?- first X.", 1,
        [("X", "red")], "no."),
    ("failure after cut discards later clauses", "?- failedcut X.", 0,
        [], "no."),
    ("callee cut preserves caller clauses", "?- outer X.", 1,
        [("X", "blue")], "no."),
    ("choices after cut remain available", "?- aftercut X.", 2,
        [("X", "red"), ("X", "blue")], "no."),
    ("callee cut preserves caller choice points", "?- choice X, first Y.", 3,
        [("X", "red"), ("Y", "red"), ("X", "blue"), ("Y", "red"),
            ("X", "green"), ("Y", "red")], "no."),
    ("occurs check rejects a cyclic tree", "?- X = branch X.", 0,
        [], "no."),
    ("acyclic constructed answer", "?- X = branch leaf.", 1,
        [("X", "branch leaf")], "no."),
    ("distinct constructors do not unify", "?- X = red, X = blue.", 0,
        [], "no."),
    ("true succeeds", "?- true.", 0, [], "yes."),
    ("fail has no answers", "?- fail.", 0, [], "no."),
]

for label, query, answer_count, expected_bindings, final in cases:
    entries = [query, *(["y"] * answer_count)]
    beta = run("Hol --test", entries)
    native = run("V1 --test --strict", entries)
    check(bindings(beta) == expected_bindings and results(beta) == [final],
        f"invalid BETA reference for {label}", beta)
    check("BETA compatibility:" not in native and "error: [" not in native,
        f"strict native case did not use the VM: {label}", native)
    equivalent(label, beta, native)

# Both public entry points must select the same native backend.
alias_entries = ["?- choice X.", "y", "y", "y"]
equivalent("Hol --v1 dispatcher", run("V1 --test --strict", alias_entries),
    run("Hol --v1 --test --strict", alias_entries))

higher = ["?- pi p\\ p => p.", "?- 1 > 0."]
for query in higher:
    beta = run("Hol --test", [query, "?- true."])
    strict = run("V1 --test --strict", [query, "?- true."])
    check("error: [" not in strict and "BETA compatibility:" not in strict,
        "higher-order/arithmetic query did not execute in native strict mode", strict)
    equivalent("full native strict query", beta, strict)

# Reload must retain the V1 compiler and full native interpreter.
reloaded = run("V1 --test --strict --dump-bytecode", [
    "?- choice X.", "n", ":reload", higher[0], "?- choice X.", "n",
])
check(reloaded.count("Ok, one module loaded.") == 2,
    "reload did not install the module again", reloaded)
check("HOL V1 bytecode version 2" in reloaded
    and "BETA compatibility:" not in reloaded and "error: [" not in reloaded,
    "reload lost the selected full native runtime", reloaded)
check(bindings(reloaded) == [("X", "red"), ("X", "red")]
    and results(reloaded) == ["yes.", "yes.", "yes."],
    "reload changed native answers", reloaded)

dump = run("V1 --test --strict --dump-bytecode", ["?- choice X, X = blue.", "y"])
check(re.search(r"(?m)^CODE \d+ CALL\b", dump)
    and re.search(r"(?m)^CODE \d+ UNIFY\b", dump),
    "bytecode dump omitted call or unification instructions", dump)
check(bindings(dump) == [("X", "blue")] and results(dump) == ["no."]
    and "BETA compatibility:" not in dump and "error: [" not in dump,
    "dump mode changed the native search", dump)

artifact = directory / "choice.hbc"
emitted = run(f"V1 --test --strict --emit-bytecode={artifact}",
    ["?- choice X.", "y", "y", "y"])
check(artifact.is_file() and artifact.stat().st_size > 0,
    "emit-bytecode did not save the compiled query", emitted)
check(bindings(emitted) == [("X", "red"), ("X", "blue"), ("X", "green")]
    and results(emitted) == ["no."] and "error: [" not in emitted,
    "saving bytecode changed the query search", emitted)

# The saved program must remain executable without its source module.
source.unlink()
standalone = subprocess.run(
    [binary], input=f"V1 --test --run-bytecode={artifact}\n", text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=8,
)
check(standalone.returncode == 0, "saved bytecode could not execute independently",
    standalone.stdout)
check(bindings(standalone.stdout) == bindings(emitted)
    and results(standalone.stdout) == ["no."]
    and standalone.stdout.count("HolV1> Answer ") == 3,
    "standalone bytecode changed the complete answer sequence", standalone.stdout)
check("Hol =<<" not in standalone.stdout and "Compiling " not in standalone.stdout
    and "BETA compatibility:" not in standalone.stdout,
    "standalone bytecode unexpectedly requested source or used compatibility",
    standalone.stdout)

malformed = directory / "malformed.hbc"
malformed.write_text("not a HOL bytecode artifact\n")
rejected = subprocess.run(
    [binary], input=f"V1 --test --run-bytecode={malformed}\n", text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=8,
)
check(rejected.returncode != 0 and "[HolV1-BytecodeError]" in rejected.stdout
    and not bindings(rejected.stdout) and not results(rejected.stdout),
    "malformed artifact did not fail with a bytecode diagnostic", rejected.stdout)

print("V1 native answers, cut, occurs check, higher-order execution, reload, dump and standalone artifacts passed")
PY
