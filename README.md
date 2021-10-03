# ppap

- Project Putting All Power!

- In `Windows 10`, everything works fine.

# Quick Start

```
git clone https://github.com/KiJeong-Lim/ppap.git
cd ppap
stack build ppap --ghc-options="-O3"
stack exec -- ppap
Copyright (c) 2020-2021, Kijeong Lim
All rights reserved.

ppap =<< Aladdin
ppap >>= exec (Aladdin.main)
Aladdin =<< ndc
aladdin> Compiling ndc    ( C:\\Users\user\Repository\ppap\ndc.aladdin, interpreted )
ndc> Ok, one module loaded.
ndc> ?- example1.
ndc> yes.
ndc> ?- X = s Y.
ndc> The answer substitution is:
ndc> X := s Y.
ndc> Find more solutions? [Y/n] Y
ndc> no.
ndc> :q
Aladdin >>= quit
```

# Aladdin

- My dialect of lambda-Prolog

# LGS

- My lexer generator

# PGS

- My parser generator

# Calc

- My calculator
