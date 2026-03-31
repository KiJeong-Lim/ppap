## Quick Start

```
$ stack exec -- ppap
ppap> Copyright (c) 2021-2026, Kijeong Lim
ppap> All rights reserved
ppap =<< Hol
ppap >>= exec (Hol.main)
Hol =<< Example/einstein.hol
Hol> Compiling Example.einstein ( Example/einstein.hol, interpreted )
Example.einstein> Ok, one module loaded.
Example.einstein> ?- answer Houses.
Example.einstein> The answer substitution is:
Example.einstein> Houses := [house norway water dunhill cat yellow, house denmark tea blend horse blue, house england milk pallmall bird red, house german coffee prince ?V_411827 green, house sweden beer bluemaster dog white].
Example.einstein> Find more solutions? [Y/n] y
Example.einstein> no.
Example.einstein> :q
Hol >>= quit
```

# ppap

- Project Putting All Power!

- In `Windows 10`, everything works fine.

## Aladdin

- My subset of λProlog, which uses higher-order pattern unification.

## Calc

- ~~My calculator, which is aimed at replacing Matlab.~~

## Jasmine

- ~~My dialect λProlog, which has Haskell-like syntax.~~

## LGS

- My lexer generator, which supports the positive lookahead operator `/`.

## PGS

- My parser generator, which generates LALR(1) parsers.
