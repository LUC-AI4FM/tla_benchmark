---- MODULE EvenRange ----
EXTENDS Integers

VARIABLE s

F(x) == x \in 0..9 /\ x % 2 = 0

Init == s = 0

Spec == Init /\ [][F(s')]_s
====