# ppap

> Projects Pouring All Power.

`ppap` is a collection of Haskell research and experiment projects packaged behind one executable. The public-facing documentation focuses on the logic programming interpreter, lexer/parser generators, and calculation experiments.

- `Hol`: a lambda Prolog-style logic programming interpreter. The default implementation is currently `Hol.BETA2`.
- `LGS`: a lexer generator.
- `PGS`: a parser generator.
- `Calc`: calculation experiments, including Presburger arithmetic and control-system diagrams.
- `TEST`: a helper entry point for repository smoke tests.

## Quick Start

```bash
cabal build ppap
cabal run -v0 ppap
```

`ppap` starts as an interactive dispatcher. For example, open the `Hol` REPL like this:

```text
ppap =<< Hol
Hol =<< example/fibonacci
example.fibonacci> ?- main N.
example.fibonacci> :q
```

You can also pass a one-shot dispatcher transcript through standard input.

```bash
printf 'Hol --test\nexample/fibonacci\n?- main N.\n:q\n\n' | cabal run -v0 ppap
printf 'TEST\nholsmoke\n' | cabal run -v0 ppap
```

The project can also be built with Stack.

```bash
stack build
```

## Requirements

The basic build requires a Haskell toolchain.

- Cabal or Stack
- GHC

## Repository Layout

```text
src/
  Main.hs                  top-level dispatcher
  Hol/BETA2/               current Hol implementation
  LGS/, PGS/               lexer/parser generators
  Calc/                    arithmetic and control-system experiments
  Json/                    generated lexer/parser example
  Z/, Y/, X/               shared utilities, pretty printing, C FFI helper

test/                      Hol regression and smoke fixtures
example/                   sample .hol programs and generator inputs
doc/                       design notes and local coding guidelines
```

## Top-Level Commands

The executable accepts these dispatcher commands:

```text
Hol [--pretty|--test]
Calc
LGS
PGS
TEST
```

Arguments must be passed in `--arg` form because the top-level dispatcher parses command lines itself.

```bash
printf 'Hol --test\nexample/fibonacci\n?- main N.\n:q\n\n' | cabal run -v0 ppap
printf 'TEST\nholsmoke\n' | cabal run -v0 ppap
```

## Hol

`Hol` is a small lambda Prolog-style language with higher-order abstract syntax, typed terms, modules, notation support, Presburger arithmetic constraints, and a debugger-oriented REPL.

Useful REPL commands:

```text
:q          quit
:reload     reload the current module
:d          toggle debugging
:short      use compact type display
:verbose    use verbose type display
:show ?X    show a logic variable while debugging
:assign ?X := term
```

Examples live under `example/*.hol` and `test/**/*.hol`.

```bash
cabal run -v0 ppap
# then:
# ppap =<< Hol
# Hol =<< example/stlc
# example.stlc> ?- infer (anno (lam x\ x) (fn A A)) T.
```

## LGS and PGS

`LGS` and `PGS` are source generators. They read a `.txt` specification and write a sibling `.hs` file. If generation fails, they write a `.failed` file.

```bash
printf 'LGS\nexample/BETA2/PlanHolLexer.txt\n\n' | cabal run -v0 ppap
printf 'PGS\nexample/BETA2/PlanHolParser.txt\n\n' | cabal run -v0 ppap
```

Generated files such as `PlanHolLexer.hs` and `PlanHolParser.hs` should be regenerated from their `.txt` sources rather than edited by hand.

## Tests

Run the Hol smoke suite:

```bash
./test/smoke.sh
```

Refresh expected outputs while authoring tests:

```bash
./test/smoke.sh --update
```

## Development Notes

- Local Haskell style notes are in `doc/llm-guideline.md`.
- Generated files should be regenerated from their source specs where possible.
- The repository contains several experiments under one executable, so prefer changing the smallest relevant module and running the focused smoke test afterward.

## License

BSD-3-Clause. See [`LICENSE`](LICENSE).
