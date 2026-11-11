# Changelog

LoL has no release yet. Entries are grouped by the milestones of [`doc/LoL_plan.md`](../doc/LoL_plan.md), newest first. Times are YYYY-MM-DD HH:MM in KST; entries written before 2026-11-11 04:27 carry the date only.

## LoL ALPHA1 (in development)

### M1. Kernel I: the core without inductive types (done)

The entries from 2026-11-11 17:59 on consolidate M1. They change the Hol engine and the way the host drives it. The kernel `lol/hol/kernel.hol` is unchanged.

#### 2026-11-11 20:23: the collector skips the program, clause shapes are read once, no depth limit is left

Changed

- `doc/LoLALPHA1.txt`, 5.2, and its Korean version: a run sees the facts of one environment. The host may keep them loaded between the runs on that environment, or give a run only the facts of the declarations it depends on; the kernel looks a constant up by its number, so the result is the same.
- Hol V1: the part of a program that precedes its first variable is sealed when it is loaded. A collection neither visits nor moves it. A program given in fragments has no variable and is sealed as a whole, so a collection on the engine costs what the run costs.
- Hol V1: the shape of a global fact (its binders, head and body) is read once, when the fact is loaded. A search starts from the spine that the machine already has of its goal. A spine keeps up to six arguments in itself, and the unifier keeps its buffers between two unifications.
- Hol V1: the full normal form of an application visits its function part once. It used to normalize that part twice at every level, which made an application with n arguments cost n squared.

Fixed

- The three traversals that still stopped at 8192 levels are loops now: the import and the export of a term sent to or by the host, and the unification of the arguments of a rigid term. No term operation limits the depth of a term.

Added

- `test/v1/probe.sh` runs the conversion checker of the plan's Appendix A and a normal form 16384 applications deep on the kernel, each under a time budget of about ten times its present time and a 2 GiB limit on its address space. `./test/smoke.sh` includes it.
- [`doc/LoL_plan.md`](../doc/LoL_plan.md), Section 14, lists the optimization work that remains in one table (O1 to O12).

Measured

| run | before | after |
|-----|--------|-------|
| unary conversion test, `mul 100 100` against 10000 | 0.39 s | 0.28 s |
| the same for `mul 200 200` against 40000 | 1.4 s | 1.06 s |
| normal form of `mul 256 256` on Church numerals | 1.4 s | 1.30 s |
| normal form of the last link of a chain of 51200 definitions | 0.75 s | 0.30 s |
| one declaration in a chain | 0.15 ms | 0.13 ms |
| normalizing an application with 20000 arguments and a variable | 0.79 s | 0.001 s |

The engine alone, on the same wordcode: the conversion test 0.37 s to 0.26 s, `mul 256 256` 1.40 s to 1.20 s.

Verified

- A collection over a sealed program of 200000 nodes allocates less than 16 kB. A pair nested 200000 times in its first component and a constant applied to 200000 arguments are written, read and unified.
- The 127 native fixtures (also with a collection before every goal), the 214 comparisons of unification with the BETA interpreter, and the host and runtime tests pass unchanged.
- `./test/smoke.sh`: 168 passed, 0 failed (2026-11-11 20:22).

Known limits

- What remains is in the table of [`doc/LoL_plan.md`](../doc/LoL_plan.md), Section 14: the REPL compiles its module for every query (O1), the engine holds one environment and loads another one again at every switch (O3), terms that still contain variables are rebuilt when they are bound (O4), and the table of identities costs an insertion and a removal for every variable (O12).

#### 2026-11-11 19:43: the kernel keeps one machine, and facts are found by their first argument

Added

- Hol V1: a machine keeps its program across runs. Wordcode comes in fragments: `hol_v2_extend` adds the symbols and clauses of a fragment to the program, `hol_v2_query` runs the query of a fragment, and `hol_v2_idle` leaves the run. Leaving a run returns the machine to the state of a new machine with the same program, so every run numbers its variables alike.
- Hol V1: global facts are indexed by their first argument, when that is a natural literal or has an ordinary constant as its head. The index leaves out only facts that the search would have skipped without a trial, so answers and their order are unchanged.
- Hol V1, Haskell: `loadPreparedProgram`, `extendLoadedProgram` and `queryLoadedProgram` compile fragments, and `Full.Engine` (`createEngine`, `extendEngine`, `withQuery`, `leaveEngine`, `closeEngine`) is a machine that keeps its program.
- `LoL.Env`: `Mode`, `declareIn`, `askIn` and `allFacts`. `Persistent` runs on the engine that the kernel keeps, and `Reference` runs as before, on a new machine with the facts of the declarations the run depends on.

Changed

- The kernel keeps one engine that holds its clauses and the facts of one environment. A declaration is checked on it, and an admitted declaration adds its one or two facts to it. Nothing of the environment is compiled or loaded again.
- `Env` is still a value: every environment remains usable, in any order, and branches of one environment may number their constants alike. An environment with declarations has a stamp of its own. A run on an environment whose stamp the engine does not hold builds the engine again from the declarations of that environment.
- `Env` is abstract. Only `declare` makes an environment with declarations; `envDecls`, `envNames` and `envFresh` read one. Two environments are equal when their declarations are.
- A run on the engine has every fact of its environment at hand, where a run used to get the facts of the declarations it depends on. The kernel looks a constant up by its number, so the run reaches the same facts.

Measured (small definitions declared one after another through the host; the former path is `Reference`)

| experiment | new machine for each run | one engine |
|------------|--------------------------|------------|
| 800 independent declarations | 0.68 s | 0.17 s |
| a chain of 200, each depending on the one before | 0.31 s | 0.03 s |
| a chain of 400 | 1.04 s | 0.06 s |
| a chain of 800 | 3.96 s | 0.12 s |
| a chain of 1600 | 18.4 s | 0.24 s |
| a chain of 12800 | not run | 1.9 s, 60 MB |
| a chain of 51200 | not run | 7.6 s, 170 MB |

A declaration costs 0.15 ms whatever came before it. Going back to an environment that the engine does not hold costs 0.10 s for 12800 declarations and 0.43 s for 51200. The normal form of the last link of the chain of 12800, which unfolds 12800 definitions, takes 0.10 s.

The index also helps runs that have no table of facts, because the clauses of the kernel are selected by the constructor of their first argument: the engine alone runs `mul 256 256` to its normal form in 1.37 s instead of 1.51 s, and the unary conversion test in 0.35 s instead of 0.38 s.

Verified

- Every native fixture whose clauses mention no query variable also runs in fragments: a seed, two additions and the query three times, once after a run that was left early. Malformed fragments and allocation failures are covered, under ASan and UBSan.
- `test/v1/full_compiler.sh` decodes the fragments of each program and compares them with the whole program. `test/v1/full_runtime.sh` runs an engine against new machines before and after its program grows.
- `test/lol/host.sh` asks the same questions of the engine and of new machines across three branches of one environment that give constant 7 to an axiom, a numeral and a theorem, in mixed order, and compares every verdict. It replays the declarations in `Reference` mode and compares the environments.
- `./test/smoke.sh`: 167 passed, 0 failed (2026-11-11 19:43).

Known limits

- The engine holds one environment. Every switch to another one loads that environment again, at about 8 microseconds for each declaration.
- A fact that was loaded is never removed, and the term heap of the engine shares nothing between declarations: about 3 kB for each small declaration, the Haskell value included.
- A collection of the engine visits the whole program, so a long run on a large environment pays for the size of the environment at every collection.
- `doc/LoLALPHA1.txt`, 5.2, said that a run receives the facts of the declarations that the checked declaration depends on. That is what `Reference` does; the engine holds more facts than that. The paragraph was rewritten in the next entry.

#### 2026-11-11 18:35: a declaration costs a tenth of what it did

Changed

- The host compiles the clauses of the kernel once, when it loads the kernel (`prepareFullProgram`), and for each declaration only the query and the facts of the declarations it depends on (`compilePreparedProgram`). `Kernel` holds the compiled clauses instead of the source facts.

Fixed

- Both Hol compilers took the index of a new template from `IntMap.size`, which walks the whole table: compiling was quadratic in the number of templates. The index now comes from the size of a key map.
- The bytecode validator walked the list of digits from its start for every natural literal. It now builds one set of positions.
- The C machine no longer tries a clause whose natural argument differs from that of the goal, as in a lookup `cst_type N A`.

Measured (small definitions declared one after another through the host)

| experiment | before | after |
|------------|--------|-------|
| 800 independent declarations | 6.76 s | 0.72 s |
| a chain of 200, each depending on the one before | 3.99 s | 0.55 s |
| a chain of 400 | 13.9 s | 2.08 s |
| a chain of 800 | 62.8 s | 9.6 s |

`./test/lol/kernel.sh --engine v1`, which compiles the kernel for every query, went from 4.26 s to 1.46 s.

Verified

- `test/v1/full_compiler.sh` compares a program whose facts were compiled ahead, all of them or half of them, with the program compiled in one go: clauses, query, variables, symbols and environments.
- `./test/smoke.sh`: 167 passed, 0 failed (2026-11-11 18:38), with everything of the three entries of this day.

Known limits

- A chain is still quadratic: every declaration compiles, validates and loads the facts of everything it depends on. Removing that needs an engine that keeps a program and accepts further facts and queries, which is planned for Hol V2.


#### 2026-11-11 18:35: no limit on the depth of a term

Fixed

- A term nested deeper than 8192 levels was refused with `Term nesting exceeds the native work stack`. Substitution, normalization, eta-reduction, the abstraction of a value over a nominal, the occurs and scope checks and equality now keep their pending steps in an array of the term store instead of the C stack.
- With deep results the collector became the bottleneck: it retired the identities it freed one at a time and moved 289 GB of memory in one run. It now merges them into the retired intervals in one pass (11 MB).

Measured (`norm (mul n n)` on Church numerals, as in the entry below)

| n | depth of the result | before | after |
|---|---------------------|--------|-------|
| 96 | 9216 | refused | 0.19 s, 41 MB |
| 128 | 16384 | refused | 0.33 s, 54 MB |
| 256 | 65536 | refused | 1.54 s, 154 MB |
| 316 | 99856 | refused | 2.31 s, 223 MB |

Verified

- A test of the term store on terms 200,000 applications deep, and `test/lol/host.sh` on the normal form of 128 × 128, its conversion with the numeral of 16384, and the rejection of its conversion with 128.

Known limits

- Three traversals still stop at 8192 levels: the import of a term sent by the host, the function side of an export, and the arguments of a rigid term other than the last during unification. None of them is on the path of a kernel run.
- On shallow terms the array is slightly slower than recursion: the conversion test below went from 0.36 s to 0.39 s.


#### 2026-11-11 17:59: large normal forms no longer cost the square of their size

Fixed

- `Compute` on a term with a large normal form took time and memory that grew with the square of the result. There were two causes, both in the V1 engine.
    - Every `=` goal of the kernel stopped the C machine and went to the Haskell host, which decoded both sides only to answer "no arithmetic here, search on". The exported variables could never be collected.
    - The C term store skipped ground terms only. A term built under `pi x\` contains the nominal `x`, so binding a variable to it normalized, copied and scanned the whole term, several times.
- The term store now keeps a summary in every node. A node with no variable below it is stable; for a stable node the store knows whether it is normal, the largest scope of its nominals and the range of its loose bound indices. Traversals do not enter a stable subterm when its summary answers their question, and binding a variable to a stable term shares the term.
- Unification normalizes its two terms once, no longer normalizes and compares the arguments of a rigid term at every level, and solves the last argument of a term without recursion.
- The C machine itself decides an equality without arithmetic and an implication whose antecedent gives the host no premise. A run of the kernel now makes no host stop until it prints a report or answers.

Measured (V1 engine, whole process, `norm (mul n n)` on Church numerals)

| n | before | after |
|---|--------|-------|
| 32 | 2.41 s, 127 MB | 0.04 s, 27 MB |
| 48 | 26.57 s, 664 MB | 0.06 s, 28 MB |
| 64 | fails after about 47 s at 1 GB | 0.10 s, 33 MB |
| 90 | not run | 0.21 s, 42 MB |

The time is now proportional to the size of the result. A conversion test on unary numerals, `mul 100 100` against 10000, went from 0.58 s to 0.36 s.

Verified

- Three new tests of the term store, ten new fixtures of the C machine and one new case in `test/lol/host.sh` (the normal form of 64 × 64 is the numeral of 4096). The C tests run under the sanitizers and against the Haskell reference unifier (214 generated cases).
- `./test/smoke.sh`: 167 passed, 0 failed.

Known limits

- A term that still contains logic variables is copied when a variable is bound to it, as before.
- The two limits found here, the depth of 8192 and the 9 ms that a declaration cost, are the subject of the two entries above.


#### 2026-11-11 04:27: the host

Added

- `src/LoL/Core.hs` (47 lines of code): Core terms with de Bruijn indices. Equality is alpha-equivalence.
- `src/LoL/Hol/Embed.hs` (95): Core terms to Hol terms and back, the facts `cst_type` and `cst_body`, the goals of a ground run, and the reports of a rejection.
- `src/LoL/Hol/Session.hs` (122): loads the kernel once and performs ground runs. A run is admitted, rejected with the first report, or undecided.
- `src/LoL/Env.hs` (105): declares an axiom, a definition or a theorem through a ground run; gives a run only the facts of the declarations it depends on; computes the assumptions of a constant; asks for a type or a normal form.
- `test/lol/host.sh` with `HostRegression.hs`.

The host has no reduction, conversion, unification or typing rule: every such question is a query to the kernel.

Verified

- 2000 generated terms survive Core to Hol and back, and 40 of them survive a trip through the engine.
- Declarations are admitted or rejected with the expected rule label, also when given through the host: `[T-Conv]`, `[T-Const]`, `[D-Ax]`.
- A theorem does not reduce and a definition does; the facts given to a run stop at the type of a theorem.
- A query with a logic variable is not run; an answer that still has a logic variable or a residual constraint does not admit; a run that reaches the time limit or the work limit is undecided, and the kernel is usable afterwards.
- Exchanging the definition and the type of a `let` in the embedding, in both directions at once, is detected.
- `./test/smoke.sh`: 167 passed, 0 failed (2026-11-11 04:28), with `test/lol/host.sh` and `test/lol/kernel.sh` among them.


#### 2026-11-11: `flex` is a builtin of Hol

Changed

- Hol has a builtin `flex T`: it holds when the head of `T` is an unbound logic variable, and it binds nothing (`doc/HolBETA.txt`, 3.6). The BETA interpreter and the V1 engine both implement it; on V1 the C machine decides it without a host stop.
- `lol/hol/kernel.hol` uses the builtin. Its own definition by double negation is gone, and the file is 130 lines of code.

Verified

- `test/flex/flex.hol`: 16 queries with the same answers on BETA and on V1; 8 fixtures for the C machine, run under the sanitizers.
- The 95 kernel tests and the 16 mutation files give the same results as before.
- On V1 a conversion-heavy run went from 10.8 s to 4.0 s, and the normal form of 32 × 32 from 3.1 s to 2.6 s.

#### 2026-11-11: the kernel program and its tests

Added

- `lol/hol/kernel.hol`, the kernel as a Hol program (135 lines of code). It implements these rules of LoLCore:
  - sorts and products: `[S-Prop]`, `[S-Type]`, `[P-Prop]`, `[P-Type]`, `[P-Max]`;
  - typing: `[T-Var]`, `[T-Sort]`, `[T-Const]`, `[T-Pi]`, `[T-Lam]`, `[T-App]`, `[T-Let]`, `[T-Conv]`;
  - reduction: `[R-Beta]`, `[R-Zeta]`, `[R-Local]`, `[R-Delta]`;
  - conversion and cumulativity: `[Eq-Red]`, `[Eq-Eta]`, `[C-Conv]`, `[C-Sort]`, `[C-Prop]`, `[C-Type]`, `[C-Pi]`;
  - declarations: `[D-Ax]`, `[D-Def]`, `[D-Thm]`;
  - normal forms for `Compute`.
- A rejection prints a report `rep "Label" [terms]` naming the rule that failed.
- `test/lol/kernel.sh`, a runner for kernel-level tests, and 95 tests in five modules:
  - `pts.hol`: sorts, products, typing, reduction, η and cumulativity on closed terms;
  - `church.hol`: constants and δ, with Church numerals;
  - `leibniz.hol`: Leibniz equality with its symmetry, transitivity and congruence;
  - `holes.hol`: the kernel on terms with holes (it fails, returns the hole, or unifies; it never enumerates terms);
  - `paradox/hurkens.hol`: Hurkens' paradox.
- 15 mutation files under `test/lol/mutants/` and one under `test/lol/paradox/`.

Verified

- The 95 tests pass on the Hol BETA interpreter and on the V1 general engine.
- Every mutation is detected by the tests it names.
- The kernel rejects Hurkens' derivation of `False`, and the kernel with `[S-Type]` weakened admits it (0.03 to 0.04 s and 22 MB for each of its eleven declarations on V1).
- The declarations of `church.hol`, `leibniz.hol` and `hurkens.hol` were also given to Rocq 9.0.0 (`rocq compile -noinit`), which admits and rejects the same ones.

Known limits

- The BETA interpreter runs out of memory (3 GB limit) on Hurkens' derivation under the weakened kernel, so mutation files run on V1.
- Computing a large normal form is slow on V1: with the kernel of this entry, the normal form of a product of Church numerals takes 0.27 s for 16 × 16, 3.1 s for 32 × 32 and 51 s for 64 × 64, where it ends in `Term allocation failed` (47 s, with the same end, after `flex` became a builtin). The time grows with the square of the size of the result. The BETA interpreter exceeds the memory limit already at 8 × 8.

### M0. Specifications

#### 2026-11-11: approved

- `doc/LoLCore.txt`: the theory. Section 7.4 commits a later version to a guard condition as strong as Rocq's.
- `doc/LoLALPHA1.txt` and its Korean version `doc/LoLALPHA1_ko.txt`: parts and boundaries, surface language, elaboration, the kernel program, export, files, diagnostics and tests.
- `doc/LoL_plan.md`: milestones and gates.
