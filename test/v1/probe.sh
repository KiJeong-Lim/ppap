#!/usr/bin/env bash
# test/v1/probe.sh — time and memory budgets for the general engine.
#
# Runs the conversion checker of doc/LoL_plan.md, Appendix A, and a large
# normal form on the LoL kernel through `V1 --test --general`. Every run has a
# wall-clock budget of about ten times what it took on 2026-11-11 and a limit
# on its address space. The budgets catch a return of quadratic time or of
# unbounded memory, not a small slowdown.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
if [ -z "${PPAP_BIN-}" ]; then
    cabal build ppap >/dev/null 2>&1 || {
        echo "probe.sh: cabal build ppap failed"
        exit 2
    }
    PPAP_BIN="$(cabal list-bin ppap 2>/dev/null)" || {
        echo "probe.sh: could not locate the ppap executable"
        exit 2
    }
fi

tmp_dir=$(mktemp -d "$PWD/test/v1/tmp.XXXXXX")
trap 'rm -rf -- "$tmp_dir"' EXIT

python3 - "$PPAP_BIN" "$tmp_dir" <<'PY'
from pathlib import Path
import resource
import subprocess
import sys
import time

binary = str(Path(sys.argv[1]).resolve())
directory = Path(sys.argv[2])
MEMORY = 2 * 1024 ** 3

CHECKER = r"""kind tm type.

type prop tm.
type typ (nat -> tm).
type prod (tm -> (tm -> tm) -> tm).
type lam (tm -> (tm -> tm) -> tm).
type app (tm -> tm -> tm).
type nat_ty tm.
type zero tm.
type succ (tm -> tm).
type nat_elim (tm -> tm -> tm -> tm -> tm).
type eq (tm -> tm -> tm -> tm).
type refl (tm -> tm -> tm).
type eq_elim (tm -> tm -> tm -> tm -> tm -> tm -> tm).
type add tm.
type mul tm.

type unfold (tm -> tm -> o).
type whnf (tm -> tm -> o).
type whnf_app (tm -> tm -> tm -> o).
type whnf_nat_elim (tm -> tm -> tm -> tm -> tm -> o).
type whnf_eq_elim (tm -> tm -> tm -> tm -> tm -> tm -> tm -> o).
type conv (tm -> tm -> o).
type conv_whnf (tm -> tm -> o).

unfold add (lam nat_ty (m\ lam nat_ty (n\ nat_elim (lam nat_ty (x\ nat_ty)) n (lam nat_ty (k\ lam nat_ty (ih\ succ ih))) m))).
unfold mul (lam nat_ty (m\ lam nat_ty (n\ nat_elim (lam nat_ty (x\ nat_ty)) zero (lam nat_ty (k\ lam nat_ty (ih\ app (app add n) ih))) m))).

whnf (app M N) R :- !, whnf M M1, whnf_app M1 N R.
whnf (nat_elim P Z S N) R :- !, whnf N N1, whnf_nat_elim N1 P Z S R.
whnf (eq_elim A X P D Y E) R :- !, whnf E E1, whnf_eq_elim E1 A X P D Y R.
whnf C R :- unfold C B, !, whnf B R.
whnf M M.

whnf_app (lam A F) N R :- !, whnf (F N) R.
whnf_app M N (app M N).

whnf_nat_elim zero P Z S R :- !, whnf Z R.
whnf_nat_elim (succ K) P Z S R :- !, whnf (app (app S K) (nat_elim P Z S K)) R.
whnf_nat_elim N P Z S (nat_elim P Z S N).

whnf_eq_elim (refl B W) A X P D Y R :- !, whnf D R.
whnf_eq_elim E A X P D Y (eq_elim A X P D Y E).

conv M M :- !.
conv M N :- whnf M M1, whnf N N1, conv_whnf M1 N1.

conv_whnf M M :- !.
conv_whnf (prod A F) (prod B G) :- conv A B, pi x\ conv (F x) (G x).
conv_whnf (lam A F) (lam B G) :- conv A B, pi x\ conv (F x) (G x).
conv_whnf (app M N) (app M1 N1) :- conv_whnf M M1, conv N N1.
conv_whnf (succ M) (succ N) :- conv M N.
conv_whnf (nat_elim P Z S N) (nat_elim P1 Z1 S1 N1) :- conv_whnf N N1, conv P P1, conv Z Z1, conv S S1.
conv_whnf (eq A X Y) (eq A1 X1 Y1) :- conv A A1, conv X X1, conv Y Y1.
conv_whnf (refl A X) (refl A1 X1) :- conv A A1, conv X X1.
conv_whnf (eq_elim A X P D Y E) (eq_elim A1 X1 P1 D1 Y1 E1) :- conv_whnf E E1, conv A A1, conv X X1, conv P P1, conv D D1, conv Y Y1.

type num (nat -> tm -> o).
type p10 (tm -> tm -> o).
type p100 (tm -> tm -> o).
type p1000 (tm -> tm -> o).
type p10000 (tm -> tm -> o).
type bench (string -> o).

num 0 zero.
num N (succ M) :- N > 0, K is N - 1, num K M.
p10 X (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ X)))))))))).
p100 X Y :- p10 X A, p10 A B, p10 B C, p10 C D, p10 D E, p10 E F, p10 F G, p10 G H, p10 H I, p10 I Y.
p1000 X Y :- p100 X A, p100 A B, p100 B C, p100 C D, p100 D E, p100 E F, p100 F G, p100 G H, p100 H I, p100 I Y.
p10000 X Y :- p1000 X A, p1000 A B, p1000 B C, p1000 C D, p1000 D E, p1000 E F, p1000 F G, p1000 G H, p1000 H I, p1000 I Y.

% unary 100 * 100 against 10000, built by clauses and by arithmetic; 200 * 200
bench "conversion" :- p100 zero H, p10000 zero T, conv (app (app mul H) H) T.
bench "counted conversion" :- p100 zero H, num 10000 T, conv (app (app mul H) H) T.
bench "larger conversion" :- p100 zero H, p100 H H2, p10000 zero T1, p10000 T1 T2, p10000 T2 T3, p10000 T3 T, conv (app (app mul H2) H2) T.
bench "counting" :- num 10000 T.
"""


def church(count):
    body = "x"
    for _ in range(count):
        body = f"app f ({body})"
    return f"(lam (typ lz) (a\\ lam (prod a (h\\ a)) (f\\ lam a (x\\ {body}))))"


# The Church numeral 128 times itself on the LoL kernel: a normal form that is
# 16384 applications deep.
KERNEL = "\n".join([
    "import lol.hol.kernel.",
    "type bench (string -> o).",
    "cst_type 0 (typ (ls lz)).",
    "cst_body 0 (prod (typ lz) (a\\ prod (prod a (h2\\ a)) (h1\\ prod a (h3\\ a)))).",
    "cst_type 4 (prod (cst 0) (h1\\ prod (cst 0) (h2\\ cst 0))).",
    "cst_body 4 (lam (cst 0) (m\\ lam (cst 0) (n\\ lam (typ lz) (a\\ lam (prod a (h6\\ a)) (f\\ app (app m a) (app (app n a) f)))))).",
    "cst_type 8 (cst 0).",
    f"cst_body 8 {church(128)}.",
    'bench "normal form" :- norm (app (app (cst 4) (cst 8)) (cst 8)) R.',
    "",
])

(directory / "checker.hol").write_text(CHECKER)
(directory / "kernel.hol").write_text(KERNEL)

# module, query, seconds allowed (seconds measured on 2026-11-11)
RUNS = [
    ("checker.hol", "conversion", 4.0),           # 0.30
    ("checker.hol", "counted conversion", 5.0),   # 0.43
    ("checker.hol", "larger conversion", 12.0),   # 1.10
    ("checker.hol", "counting", 3.0),             # 0.14
    ("kernel.hol", "normal form", 4.0),           # 0.29
]


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


failed = False
for module, query, allowed in RUNS:
    path = str((directory / module).relative_to(Path.cwd()))
    transcript = "\n".join(["V1 --test --general", path, f'?- bench "{query}".', ":q", ""])
    started = time.monotonic()
    try:
        result = subprocess.run([binary], input=transcript, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=allowed, preexec_fn=limit)
        elapsed = time.monotonic() - started
        answered = result.returncode == 0 and any(line.endswith("> yes.") for line in result.stdout.splitlines())
        verdict = "PASS" if answered else "FAIL"
        detail = "" if answered else "\n" + result.stdout[-2000:]
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - started
        verdict, detail = "FAIL", "  (over its budget)"
    failed = failed or verdict != "PASS"
    print(f"{verdict} {query}: {elapsed:.2f} s of {allowed:.0f} s{detail}")
if failed:
    raise SystemExit(1)
print("V1 probes: every run stayed within its time and memory budget")
PY
