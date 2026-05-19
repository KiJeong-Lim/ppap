stack build ppap
time (printf "Hol\nexample/test.hol\n?- main X Y Z.\ny:q\n\n" | stack exec -- ppap)
cat example/test.hol
