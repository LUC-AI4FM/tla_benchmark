---- MODULE PrimedPredicate ----
EXTENDS Integers

VARIABLE s

vars == <<s>>

F(var) == var \in 0..9 /\ var % 2 = 0

Init == s = 0

Next == F(s')

Spec == Init /\ [][F(s')]_s

TypeOK == s \in 0..9

EvenInv == s % 2 = 0

Inv == F(s)

THEOREM Spec => []Inv
====