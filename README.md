# ppap

> Projects Pouring All Power.

`ppap` is a collection of Haskell research and experiment projects packaged behind one executable. The public-facing documentation focuses on the logic programming interpreter, lexer/parser generators, and calculation experiments.

- `Hol`: a lambda Prolog-style logic programming interpreter. The default implementation is currently `Hol.BETA`.
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
  Hol/BETA/               current Hol implementation
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

The final legacy Aladdin implementation (`086a9d1`) lives in `src/Hol/ALPHA1/`. Run it with the `ALPHA1` dispatcher command; it loads `.hol` files and retains the original Aladdin syntax, with natural-number arithmetic added explicitly.

Arithmetic follows [SWI-Prolog's ordinary evaluation rules](https://www.swi-prolog.org/pldoc/man?section=arith), restricted to `nat`: `is` evaluates its right operand and unifies the result with its left operand; `=:=`, `=\=`, `<`, `=<`, `>`, and `>=` evaluate both operands. Structural `=` still unifies terms without evaluating arithmetic. Supported expressions use binary `+`, `-`, `*`, `/`, `//`, `div`, `mod`, `rem`, unary `+`/`-`, and the legacy successor `s`. The words `is`, `div`, `mod`, and `rem` are reserved arithmetic keywords. Expressions may contain previously bound variables, but an unbound variable raises `instantiation_error` immediately.

Every evaluated subexpression must be a natural number. Negative results raise `domain_error(not_less_than_zero)`, nonintegral `/` results raise `domain_error(nat)`, and division by zero raises `evaluation_error(zero_divisor)`. `/` therefore requires an exact natural quotient; `//` and `div` compute the integer quotient. For example, `?- X is 7 // 2.` gives `X := 3`, while `?- X is 7 / 2.` reports an error. These restrictions apply to arithmetic evaluation; ordinary term unification retains Aladdin's existing behavior.

ALPHA1's lexer and parser are generated from the specifications in `example/ALPHA1/` by `src/LGS/Alpha2.hs` and `src/PGS/Alpha1.hs`, respectively. The `LGS` and `PGS` dispatcher commands call these implementations. `test/typecheck/generated_sources.sh` regenerates them and checks that both the example and executable copies match byte for byte.

```bash
cabal run -v0 ppap
# then:
# ppap =<< Hol
# Hol =<< example/stlc.hol
# example.stlc> ?- infer (anno (lam x\ x) (fn A A)) T.
```

## LGS and PGS

`LGS` and `PGS` are source generators. They read a `.txt` specification and write a sibling `.hs` file. If generation fails, they write a `.failed` file.

```bash
printf 'LGS\nexample/BETA/PlanHolLexer.txt\n\n' | cabal run -v0 ppap
printf 'PGS\nexample/BETA/PlanHolParser.txt\n\n' | cabal run -v0 ppap
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
