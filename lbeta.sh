stack build ppap
time (printf "Hol\nExample/test.hol\n?- main X Y Z.\ny:q\n\n" | stack exec -- ppap)
cat Example/test.hol
