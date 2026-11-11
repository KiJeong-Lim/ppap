#!/usr/bin/env python3
"""Kernel-level tests of LoL (doc/LoLALPHA1.txt, Chapter 9).

A test module is a Hol module that imports `lol.hol.kernel` and defines

    %! admit
    test "name" :- <goal>.

    %! reject T-Conv
    test "name" :- <goal>.

`admit` means that the query `?- test "name".` has an answer. `reject L` means
that it has none and that the first report printed by `expect` carries the
rule label L of doc/LoLCore.txt.

A mutation file (`*.mut`) rewrites the kernel:

    # comment
    - <a line of lol/hol/kernel.hol; the `-` lines together occur exactly once>
    + <its replacement>
    kills <module> "<name>"     the test must not meet its expectation
    admits <module> "<name>"    the test must be admitted

Every engine run has a time limit and a memory limit.
"""

import argparse
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KERNEL = ROOT / "lol" / "hol" / "kernel.hol"
ENGINES = {
    "beta": "Hol --test",
    "v1": "V1 --test --general",
}
TIME_LIMIT = 120
MEMORY_LIMIT = 3 * 1024 * 1024 * 1024

EXPECT_RE = re.compile(r"^%!\s*(admit|reject\s+(\S+))\s*$")
TEST_RE = re.compile(r'^test\s+"([^"]+)"')
REPORT_RE = re.compile(r'^rep "([^"]+)"')
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
CLAIM_RE = re.compile(r'^(kills|admits)\s+(\S+)\s+"([^"]+)"\s*$')


class Failure(Exception):
    pass


def limit_resources():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))


def parse_module(path):
    """Return [(name, expectation)] in source order."""
    tests, pending = [], None
    for number, line in enumerate(path.read_text().splitlines(), 1):
        found = EXPECT_RE.match(line)
        if found:
            if pending is not None:
                raise Failure(f"{path}:{number}: `%!` without a test before it")
            pending = "admit" if found.group(1) == "admit" else found.group(2)
            continue
        found = TEST_RE.match(line)
        if found:
            if pending is None:
                raise Failure(f"{path}:{number}: test without a `%!` line")
            tests.append((found.group(1), pending))
            pending = None
    if pending is not None:
        raise Failure(f"{path}: `%!` without a test after it")
    names = [name for name, _ in tests]
    if len(names) != len(set(names)):
        raise Failure(f"{path}: duplicate test name")
    return tests


def parse_mutation(path):
    old, new, kills, admits = [], [], [], []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        if line.startswith("- "):
            old.append(line[2:])
        elif line.startswith("+ "):
            new.append(line[2:])
        elif CLAIM_RE.match(line):
            kind, stem, name = CLAIM_RE.match(line).groups()
            (kills if kind == "kills" else admits).append((stem, name))
        else:
            raise Failure(f"{path}:{number}: not a mutation line")
    if not old:
        raise Failure(f"{path}: no `-` line")
    if not kills and not admits:
        raise Failure(f"{path}: no `kills` or `admits` line")
    return "\n".join(old) + "\n", "\n".join(new) + "\n" if new else "", kills, admits


def mutate(kernel_text, mutation_path):
    old, new, kills, admits = parse_mutation(mutation_path)
    count = kernel_text.count(old)
    if count != 1:
        raise Failure(
            f"{mutation_path}: the `-` lines occur {count} times in the kernel"
        )
    return kernel_text.replace(old, new), kills, admits


def run_module(binary, engine, kernel_text, module):
    """Return {name: verdict}; a verdict is `admit`, a label, or `!...`."""
    tests = parse_module(module)
    with tempfile.TemporaryDirectory(prefix="lol-kernel-") as root:
        root = Path(root)
        (root / "lol" / "hol").mkdir(parents=True)
        (root / "lol" / "hol" / "kernel.hol").write_text(kernel_text)
        shutil.copy(module, root / "suite.hol")
        lines = [ENGINES[engine], "suite.hol"]
        lines += [f'?- test "{name}".' for name, _ in tests]
        lines += [":q", ""]
        try:
            done = subprocess.run(
                [binary], input="\n".join(lines), text=True, cwd=root,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=TIME_LIMIT, preexec_fn=limit_resources,
            )
        except subprocess.TimeoutExpired:
            return {name: "!timeout" for name, _ in tests}
    output = ANSI_RE.sub("", done.stdout)
    prompt = "suite> "
    blocks, current, loaded = [], None, False
    for line in output.splitlines():
        if not line.startswith(prompt):
            if current is not None:
                current.append("!" + line)
            continue
        text = line[len(prompt):]
        if not loaded:
            loaded = text.startswith("Ok,")
            continue
        if text == "":
            current = []
            blocks.append(current)
        elif current is not None:
            current.append(text)
    verdicts = {}
    for index, (name, _) in enumerate(tests):
        if not loaded:
            verdicts[name] = "!load: " + " | ".join(output.splitlines()[-3:])
        elif index >= len(blocks) or not blocks[index]:
            verdicts[name] = f"!no output (exit {done.returncode})"
        else:
            verdicts[name] = classify(blocks[index])
    return verdicts


def classify(block):
    last = block[-1]
    if last == "yes.":
        return "admit"
    if last == "no.":
        for text in block:
            found = REPORT_RE.match(text)
            if found:
                return found.group(1)
        return "!no report"
    return "!" + last


def suite_modules(arguments):
    if arguments:
        return [Path(argument).resolve() for argument in arguments]
    found = sorted((ROOT / "test" / "lol" / "kernel").glob("*.hol"))
    found += sorted((ROOT / "test" / "lol" / "paradox").glob("*.hol"))
    return found


def run_suite(binary, engines, modules):
    kernel_text = KERNEL.read_text()
    passed = failed = 0
    for module in modules:
        expectations = parse_module(module)
        for engine in engines:
            verdicts = run_module(binary, engine, kernel_text, module)
            for name, expected in expectations:
                got = verdicts[name]
                if got == expected:
                    passed += 1
                else:
                    failed += 1
                    print(f"FAIL  {engine:4}  {module.stem}:{name}"
                          f"  expected {expected}, got {got}")
            print(f"{engine:4}  {module.relative_to(ROOT)}"
                  f"  {len(expectations)} tests")
    print(f"kernel tests: {passed} passed, {failed} failed")
    return failed == 0


def run_mutants(binary, engines, mutation_paths):
    modules = {module.stem: module for module in suite_modules([])}
    kernel_text = KERNEL.read_text()
    passed = failed = 0
    for mutation_path in mutation_paths:
        mutant, kills, admits = mutate(kernel_text, mutation_path)
        for engine in engines:
            cache = {}
            problems = []
            for wanted, pairs in (("kills", kills), ("admits", admits)):
                for stem, name in pairs:
                    if stem not in modules:
                        raise Failure(f"{mutation_path}: no module {stem}")
                    if stem not in cache:
                        cache[stem] = run_module(
                            binary, engine, mutant, modules[stem])
                    expected = dict(parse_module(modules[stem])).get(name)
                    if expected is None:
                        raise Failure(f"{mutation_path}: no test {stem}:{name}")
                    got = cache[stem][name]
                    if got.startswith("!"):
                        problems.append(f"{stem}:{name} gave {got}")
                    elif wanted == "kills" and got == expected:
                        problems.append(f"{stem}:{name} still gives {got}")
                    elif wanted == "admits" and got != "admit":
                        problems.append(f"{stem}:{name} gives {got}")
            label = mutation_path.relative_to(ROOT)
            if problems:
                failed += 1
                print(f"FAIL  {engine:4}  {label}: " + "; ".join(problems))
            else:
                passed += 1
                print(f"{engine:4}  {label}  killed")
    print(f"kernel mutants: {passed} killed, {failed} not as specified")
    return failed == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--engine", choices=["beta", "v1", "both"],
                        help="default: both for the suite, v1 for mutants")
    parser.add_argument("--mutants", action="store_true",
                        help="run the mutation files instead of the suite")
    parser.add_argument("paths", nargs="*")
    options = parser.parse_args()
    binary = os.environ.get("PPAP_BIN")
    if not binary or not os.access(binary, os.X_OK):
        raise Failure("PPAP_BIN must name the ppap executable")
    # The BETA interpreter exceeds the memory limit on the mutated Hurkens
    # derivation, so mutation files run on the V1 engine unless asked.
    chosen = options.engine or ("v1" if options.mutants else "both")
    engines = ["beta", "v1"] if chosen == "both" else [chosen]
    if options.mutants:
        paths = [Path(path).resolve() for path in options.paths]
        if not paths:
            paths = sorted((ROOT / "test" / "lol" / "mutants").glob("*.mut"))
            paths += sorted((ROOT / "test" / "lol" / "paradox").glob("*.mut"))
        ok = run_mutants(binary, engines, paths)
    else:
        ok = run_suite(binary, engines, suite_modules(options.paths))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    try:
        main()
    except Failure as failure:
        print(f"kernel.py: {failure}")
        sys.exit(2)
