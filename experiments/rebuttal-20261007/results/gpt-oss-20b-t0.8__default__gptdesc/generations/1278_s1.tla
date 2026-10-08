----------------------------- MODULE SmallSpec -----------------------------
EXTENDS Integers

VARIABLE s

F(x) == x \in 0..9 /\ x % 2 = 0

Init == (s = 0)

Next == F(s')

Spec == Init /\ [] [Next]_s
=============================================================