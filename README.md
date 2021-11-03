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
Aladdin =<< Example/NDC.aladdin 
Aladdin> Compiling Example.NDC ( C:\\Users\user\source\Repositories\ppap\Example\NDC.aladdin, interpreted )
Example.NDC> Ok, one module loaded.
Example.NDC> ?- example1.
Example.NDC> yes.
Example.NDC> ?- X = s Y.
Example.NDC> The answer substitution is:
Example.NDC> X := s Y.
Example.NDC> Find more solutions? [Y/n] Y
Example.NDC> no.
Example.NDC> ?- pi (X\ F X = X). 
Example.NDC> The answer substitution is:
Example.NDC> F := W_1\ W_1.
Example.NDC> Find more solutions? [Y/n] Y
Example.NDC> no.
Example.NDC> :q
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
