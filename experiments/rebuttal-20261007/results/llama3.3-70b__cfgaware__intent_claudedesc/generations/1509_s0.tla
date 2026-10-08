------------ MODULE RecursiveFunction ------------
EXTENDS Integers

CONSTANT Domain

VARIABLE x

Rec(n) == IF n = 0 THEN 1 ELSE Rec(n-1) + 2

Init == x \in Domain

Next == x' = x

Spec == Init /\ [][Next]_x

THEOREM Spec => []<>(x \in {Rec(i) : i \in Domain})
====================================