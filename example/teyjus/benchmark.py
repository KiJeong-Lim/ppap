#!/usr/bin/env python3
"""Compare complete Einstein searches, including process startup and output."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import resource
import shutil
import statistics
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
QUERIES = {"direct": "answer Houses.", "automatic": "sigma P\\ P = answer, P Houses.", "general": "sigma P\\ P = answer, P Houses."}


def run(command, directory, stdin="", timeout=30):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter_ns()
    result = subprocess.run(command, input=stdin, text=True, cwd=directory,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    wall = (time.perf_counter_ns() - start) / 1e9
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if result.returncode or "error: [" in result.stdout:
        raise RuntimeError(f"{command}: exit {result.returncode}\n{result.stdout}")
    sample = {"wall_seconds": wall, "user_seconds": after.ru_utime - before.ru_utime,
        "system_seconds": after.ru_stime - before.ru_stime}
    return result.stdout, sample


def canonical_answers(output, teyjus=False):
    if teyjus:
        terms = re.findall(r"(?m)^Houses = ([\s\S]*?)(?=\n\s*\n|\Z)", output)
    else:
        terms = re.findall(r"(?m)^.*> Houses := (.+)\.\s*$", output)
    answers = []
    for term in terms:
        variables = {}
        tokens = []
        for token in re.findall(r"[A-Za-z_][A-Za-z_0-9]*", term):
            if token == "nil":
                continue
            if token[0].isupper() or token.startswith("_"):
                token = variables.setdefault(token, f"V{len(variables)}")
            tokens.append(token)
        if len(tokens) != 30 or any(tokens[i] != "house" for i in range(0, 30, 6)):
            raise RuntimeError(f"Unrecognized answer term: {term}")
        answers.append(tokens)
    if len(answers) != 1:
        raise RuntimeError(f"Expected one complete Einstein answer, got {len(answers)}\n{output}")
    if not teyjus and not re.search(r"> no\.\s*$", output, re.MULTILINE):
        raise RuntimeError(f"Hol did not exhaust the search\n{output}")
    return answers


def verify_fixture():
    def lines(path):
        return [line.strip() for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("%")]
    original = lines(ROOT / "example/einstein.hol")
    declarations = [line for line in original if line.startswith(("kind ", "type "))]
    declarations = [line.replace("(type)", "type") if line.startswith("kind ") else line
        for line in declarations]
    signature = lines(ROOT / "example/teyjus/einstein.sig")
    module = lines(ROOT / "example/teyjus/einstein.mod")
    clauses = [line for line in original if not line.startswith(("kind ", "type "))]
    if signature != ["sig einstein.", *declarations] or module != ["module einstein.", *clauses]:
        raise RuntimeError("Teyjus fixture differs from the Hol declarations or ordered clauses")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ppap-bin", required=True, type=Path)
    parser.add_argument("--baseline-ppap-bin", type=Path, help="Previous Hol executable for interleaved automatic and forced-general source/bytecode comparison")
    parser.add_argument("--baseline-label", default="not recorded")
    parser.add_argument("--teyjus-bin", required=True, type=Path)
    parser.add_argument("--teyjus-source", type=Path)
    parser.add_argument("--teyjus-build", default="not recorded", help="Build command and compiler flags for the supplied Teyjus binaries")
    parser.add_argument("--runs", type=int, default=9)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--cpu", type=int, help="Linux logical CPU; defaults to first allowed CPU")
    parser.add_argument("--output", type=Path, default=Path("/tmp/ppap-teyjus-results.json"))
    args = parser.parse_args()
    if args.runs < 3 or args.warmups < 1:
        parser.error("use at least 3 measured runs and 1 warmup")
    verify_fixture()
    allowed = sorted(os.sched_getaffinity(0))
    cpu = args.cpu if args.cpu is not None else allowed[0]
    if cpu not in allowed:
        parser.error(f"CPU {cpu} is outside allowed affinity {allowed}")
    ppap = str(args.ppap_bin.resolve())
    tools = {name: str((args.teyjus_bin / name).resolve()) for name in ("tjcc", "tjlink", "tjsim")}
    for executable in (ppap, *tools.values()):
        if not os.access(executable, os.X_OK):
            parser.error(f"not executable: {executable}")
    report = {
        "recorded_at": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "cpu_affinity": [cpu],
        "lscpu": subprocess.check_output(["lscpu"], text=True),
        "hol_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "hol_worktree_changes": subprocess.check_output(["git", "diff", "HEAD", "--stat"], cwd=ROOT, text=True).strip(),
        "hol_build": "GHC -O2 -funbox-strict-fields -fspec-constr -fexpose-all-unfoldings -fspecialise-aggressively; C -O3",
        "hol_rts_default": "On Linux with GHC <9.8: -V0.001; otherwise compiler defaults",
        "teyjus_version": run([tools["tjsim"], "--version"], ROOT)[0].strip(),
        "teyjus_build": args.teyjus_build,
        "ghc_version": subprocess.check_output(["ghc", "--numeric-version"], text=True).strip(),
        "benchmark_sha256": digest(Path(__file__).resolve()),
        "binary_sha256": {"ppap": digest(Path(ppap)), **{name: digest(Path(path)) for name, path in tools.items()}},
        "source_sha256": {name: digest(ROOT / name) for name in
            ("example/einstein.hol", "example/teyjus/einstein.sig", "example/teyjus/einstein.mod")},
        "compiler_sources_sha256": {name: digest(ROOT / name) for name in
            ("src/Hol/V1/Compiler.hs", "src/Hol/V1/FullCompiler.hs", "src/Hol/V1/Runtime.hs", "src/Hol/V1/Main.hs")},
        "runtime_sources_sha256": {name: digest(ROOT / name) for name in
            ("src/X/machine.c", "src/X/machine.h", "src/X/higher_machine.c", "src/X/higher_machine.h",
            "src/X/term.c", "src/X/term.h", "src/X/Machine.hs", "src/X/HigherMachine.hs",
            "src/Hol/V1/Bytecode.hs", "src/Hol/V1/FullBytecode.hs", "src/Hol/V1/FullRuntime.hs", "src/Z/Utils.hs", "ppap.cabal")},
        "queries": QUERIES,
        "selection": {"direct": "automatic dispatcher, direct call", "automatic": "automatic dispatcher, predicate alias", "general": "forced general engine via --general"},
        "method": "Fresh processes, all answers through exhaustion, stdout captured, fixed CPU, warm files, shuffled interleaving. Build/compilation excluded from replay timings.",
        "runs": args.runs, "warmups": args.warmups, "artifacts": {}, "cases": {},
    }
    if args.teyjus_source:
        report["teyjus_commit"] = subprocess.check_output(["git", "rev-parse", "HEAD"],
            cwd=args.teyjus_source, text=True).strip()
        report["teyjus_source_changes"] = subprocess.check_output(["git", "diff", "--stat"],
            cwd=args.teyjus_source, text=True).strip()
    if args.baseline_ppap_bin:
        baseline = str(args.baseline_ppap_bin.resolve())
        if not os.access(baseline, os.X_OK):
            parser.error(f"not executable: {baseline}")
        report["baseline"] = {"path": baseline, "label": args.baseline_label,
            "sha256": digest(Path(baseline)),
            "modes": ["automatic", "general"],
            "bytecode_input": "Both executables replay the same artifact emitted by the current executable; source cases each compile their own input."}
    os.sched_setaffinity(0, {cpu})
    with tempfile.TemporaryDirectory(prefix="ppap-teyjus-") as temporary:
        work = Path(temporary)
        for suffix in ("sig", "mod"):
            shutil.copyfile(ROOT / f"example/teyjus/einstein.{suffix}", work / f"einstein.{suffix}")
        report["teyjus_compile_once"] = run([tools["tjcc"], "einstein"], work)[1]
        report["teyjus_link_once"] = run([tools["tjlink"], "einstein"], work)[1]
        cases = []
        expected = None
        for mode, query in QUERIES.items():
            artifact = work / f"{mode}.hbc"
            selection = "V1 --test --strict --general" if mode == "general" else "V1 --test --strict"
            emission = f"{selection} --emit-bytecode={artifact}\nexample/einstein.hol\n?- {query}\ny\n:q\n"
            output, _ = run([ppap], ROOT, emission)
            answers = canonical_answers(output)
            if expected is None:
                expected = answers
            if answers != expected:
                raise RuntimeError("Direct and general-engine Hol queries disagree")
            prefix = "FullArtifact 2 " if mode == "general" else "BytecodeArtifact 1 "
            artifact_text = artifact.read_text()
            if not artifact_text.startswith(prefix):
                raise RuntimeError(f"Unexpected bytecode format for {mode}")
            report["artifacts"][mode] = {"sha256": digest(artifact), "bytes": artifact.stat().st_size, "format": prefix.strip()}
            source_input = f"{selection}\nexample/einstein.hol\n?- {query}\ny\n:q\n"
            cases.extend([
                (f"hol_source_{mode}", [ppap], ROOT, source_input, False),
                (f"hol_bytecode_{mode}", [ppap], ROOT, f"V1 --test --run-bytecode={artifact}\n", False),
            ])
            if mode != "automatic":
                cases.append((f"teyjus_bytecode_{mode}", [tools["tjsim"], "-b", "-e", "1", "-s", query, "einstein"], work, "", True))
            if args.baseline_ppap_bin and mode in ("automatic", "general"):
                cases.extend([
                    (f"hol_baseline_source_{mode}", [baseline], ROOT, source_input, False),
                    (f"hol_baseline_bytecode_{mode}", [baseline], ROOT, f"V1 --test --run-bytecode={artifact}\n", False),
                ])
        report["canonical_answers"] = expected
        for name, command, directory, stdin, teyjus in cases:
            report["cases"][name] = {"command": command, "stdin": stdin, "cwd": str(directory), "samples": []}
        rng = random.Random(20261110)
        for round_index in range(args.warmups + args.runs):
            order = list(cases)
            rng.shuffle(order)
            for name, command, directory, stdin, teyjus in order:
                output, sample = run(command, directory, stdin)
                if canonical_answers(output, teyjus) != expected:
                    raise RuntimeError(f"Answer mismatch: {name}\n{output}")
                item = report["cases"][name]
                item["representative_output"] = output
                if round_index >= args.warmups:
                    item["samples"].append(sample)
            print(f"Completed {'warmup' if round_index < args.warmups else 'measurement'} round {round_index + 1}/{args.warmups + args.runs}", flush=True)
        for name, item in report["cases"].items():
            times = [sample["wall_seconds"] for sample in item["samples"]]
            item["median_seconds"] = statistics.median(times)
            item["min_seconds"] = min(times)
            item["max_seconds"] = max(times)
            print(f"{name:26s} median={statistics.median(times):.6f}s range={min(times):.6f}..{max(times):.6f}s")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=4) + "\n")
        print(f"All {len(cases)} routes produced the same complete answer sequence. Results: {args.output}")


if __name__ == "__main__":
    main()
