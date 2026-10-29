---- MODULE EvenRange ----
EXTENDS Integers

VARIABLES s

vars == << s >>

F(x) == x \in 0..9 /\ x % 2 = 0

Init == s = 0

Next == F(s')

TypeOK == s \in 0..9 /\ s % 2 = 0

Spec == Init /\ [][F(s')]_s

====