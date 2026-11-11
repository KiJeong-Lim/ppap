# LoL

LoL is a proof assistant whose kernel is a λProlog program. The kernel runs on [Hol](../README.md), the λProlog implementation of this repository, and decides the typing judgments of a calculus of inductive constructions.

LoL is under development. The kernel so far covers the core without inductive types, and a Haskell host can drive it; there is no surface language yet. [Changelog.md](Changelog.md) records what exists.

## Design

- **The kernel is a logic program.** [`hol/kernel.hol`](hol/kernel.hol) implements the rules of [`doc/LoLCore.txt`](../doc/LoLCore.txt). Binders are λProlog abstractions, a local context is a set of hypotheses installed by `=>`, and every clause is preceded by the label of the rule it implements.
- **A declaration is admitted only by a run of that program.** There is no second checker written in Haskell. The Haskell side will parse, drive the engine, store and export; it implements no reduction, conversion, unification or typing rule.
- **The theory stays inside Rocq's.** A declaration that LoL admits must also be admitted by Rocq 9.0 after translation, so Rocq serves as an independent second opinion.
- **Holes and proofs use the same machinery.** A hole is a logic variable, and the elaborator and the proof mode are planned as Hol programs that call the kernel's own reduction and conversion clauses.

The specifications are [`doc/LoLCore.txt`](../doc/LoLCore.txt) (the theory) and [`doc/LoLALPHA1.txt`](../doc/LoLALPHA1.txt) (the architecture and the first language; Korean version in [`doc/LoLALPHA1_ko.txt`](../doc/LoLALPHA1_ko.txt)). The plan is [`doc/LoL_plan.md`](../doc/LoL_plan.md), in Korean.

## What the kernel checks today

| Part of LoLCore | Rules |
|---|---|
| Sorts and products | `Prop : Type@{1}`, `Type@{l} : Type@{l+1}`, impredicative `Prop`, predicative `Type@{l}` |
| Typing | variables, constants, `forall`, `fun`, application, `let` |
| Reduction | β, δ (definitions), ζ (`let`), local definitions |
| Conversion | by weak head normal forms, with η for functions |
| Cumulativity | `Prop <= Type@{l}`, `Type@{l} <= Type@{l'}` for `l <= l'`, covariant codomains |
| Declarations | `Axiom`, `Definition`, `Theorem` |

Inductive families, `match`, `fix` and the guard condition are specified in LoLCore and are the next parts of the kernel.

## Layout

| Path | Content |
|---|---|
| `lol/hol/kernel.hol` | the kernel |
| `src/LoL/Core.hs` | Core terms, as data only |
| `src/LoL/Hol/Embed.hs` | Core terms to Hol terms and back; facts, goals and reports |
| `src/LoL/Hol/Session.hs` | a ground run of the kernel and its three results: admitted, rejected, undecided; the engine that the kernel keeps |
| `src/LoL/Env.hs` | admitted declarations, the facts given to a run, assumptions |
| `test/lol/kernel/` | tests that query the kernel directly, one Hol module per topic |
| `test/lol/paradox/` | derivations of `False` that the kernel must reject, each with the kernel patch under which it is admitted |
| `test/lol/mutants/` | kernel patches, each with the tests that must detect it |
| `test/lol/kernel.sh` | the runner for the three directories above |
| `test/lol/host.sh` | builds and runs `HostRegression.hs`, the tests of the host |

## Running the tests

```bash
./test/lol/kernel.sh              # every kernel test, on the BETA interpreter and on the V1 engine
./test/lol/kernel.sh --mutants    # every kernel patch, on the V1 engine
./test/lol/host.sh                # the Haskell host against the kernel
```

`./test/smoke.sh` runs the first and the third command together with the Hol test suite.

A kernel test is a clause with its expected verdict on the line before it:

```prolog
%! admit
test "identity over Type@{0}" :-
    admit_def
        (prod (typ lz) (a\ prod a (x\ a)))
        (lam (typ lz) (a\ lam a (x\ x))).

%! reject T-Conv
test "Type@{0} : Type@{0}" :- admit_def (typ lz) (typ lz).
```

`admit_def A T` asks the kernel to admit a definition with type `A` and body `T`. The first test is `fun (a : Type@{0}) (x : a) => x` at type `forall a : Type@{0}, a -> a`. The second must be rejected, and the rejection must name the rule `[T-Conv]`.

## Asking the kernel by hand

```bash
printf 'V1 --test --general\nlol/hol/kernel.hol\n?- admit_def (typ lz) (typ lz).\n:q\n' | cabal run -v0 ppap
```

The kernel answers `no.` after printing its reason:

```text
rep "T-Conv" [typ lz, typ (ls lz), typ lz]
```

The term `typ lz` has type `typ (ls lz)`, which is not a subtype of `typ lz`: `Type@{0}` does not have type `Type@{0}`.

## Evidence for the kernel

- **Rule tests.** The tests are organised by rule label: small terms that a rule admits and small terms that it rejects. A rejection is compared by the label the kernel reports, not only by failure.
- **Paradox tests.** Hurkens' paradox is a derivation of `forall p : Prop, p` that is well typed when `Type@{0} : Type@{0}`. The kernel rejects it; the kernel with `[S-Type]` weakened to `Type@{l} : Type@{l}` admits it. Rocq 9.0.0 agrees on both counts, with and without `Unset Universe Checking`.
- **Mutation tests.** Each file under `test/lol/mutants/` plants one bug in the kernel and names the tests that must then fail.

## What a run costs

Measured on the V1 engine on 2026-11-11, whole process unless stated:

- The normal form of `mul 64 64` on Church numerals, a term 4096 applications deep: 0.08 s, 32 MB. The time is proportional to the size of the result, and the depth of a term is bounded by memory only: `mul 316 316`, 99856 deep, takes 2.05 s and 223 MB.
- A conversion test on unary numerals, `mul 100 100` against 10000: 0.28 s, 28 MB.
- Checking one small declaration through the host: 0.13 to 0.21 ms, whatever was declared before it. A chain of 12800 definitions, each depending on the one before, is admitted in 1.7 s with 58 MB.

The kernel keeps one machine that holds its clauses and the facts of one environment, and facts are found by their first argument. An environment is a value all the same: an older one, or another branch, can be used at any time, and the machine is then loaded again from its declarations (0.11 s for 12800 declarations). `declareIn Reference` checks a declaration the former way, on a new machine with the facts of the declarations it depends on; the tests compare the two.

[`doc/LoL_plan.md`](../doc/LoL_plan.md), Section 14, has the measurements and a table of the optimization work that remains. `./test/v1/probe.sh` guards the first two figures with a time and a memory budget.
