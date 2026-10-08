MODULE SmallSystem
EXTENDS Naturals, Integers

VARIABLE s

F(v) == v \in 0..9 /\ (v % 2 = 0)

Init == s = 0

Next == F(s')

Spec == Init /\ [][Next]_s