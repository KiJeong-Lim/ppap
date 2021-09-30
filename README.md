# ppap

- Project putting all power!

- In `Windows 10`, everything works fine.

# Quick Start:

```
git clone https://github.com/KiJeong-Lim/ppap.git
cd ppap
stack build ppap --ghc-options="-O3"
stack exec -- ppap
ppap =<< Aladdin
ppap >>= exec (Aladdin.main)
Aladdin =<< ndc.aladdin
aladdin> Compiling ndc  ( C:\Users\user\Repository\ppap\ndc.aladdin )
ndc> Ok, one module loaded.
ndc> ?- example1.
ndc> yes.
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
