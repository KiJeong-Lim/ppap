# ppap

- Project Putting All Power!

- In `Windows 10`, everything works fine.

# Quick Start

```
git clone https://github.com/KiJeong-Lim/ppap.git
cd ppap
stack build ppap
stack exec -- ppap
ppap> Copyright (c) 2021, Kijeong Lim
ppap> All rights reserved
ppap =<< Aladdin
ppap >>= exec (Aladdin.main)
Aladdin =<< Example/Ndc.aladdin
Aladdin> Compiling Example.Ndc ( Example/Ndc.aladdin, interpreted )
Example.Ndc> Ok, one module loaded.
Example.Ndc> ?- example1.
Example.Ndc> yes.
Example.Ndc> ?- X = s Y.
Example.Ndc> The answer substitution is:
Example.Ndc> X := s Y.
Example.Ndc> Find more solutions? [Y/n] Y
Example.Ndc> no.
Example.Ndc> ?- pi (X\ F X = X).
Example.Ndc> The answer substitution is:
Example.Ndc> F := W_1\ W_1.
Example.Ndc> Find more solutions? [Y/n] Y
Example.Ndc> no.
Example.Ndc> :q
Aladdin >>= quit
Aladdin >>= quit
```

# Aladdin

- My subset of λProlog, which uses higher-order pattern unification.

# Calc

- My calculator, which is aimed at replacing Matlab.

# Jasmine

- My dialect λProlog, which has Haskell-like syntax.

# LGS

- My lexer generator, which supports the positive lookahead operator `/`.

# PGS

- My parser generator, which generates LALR(1) parsers.
