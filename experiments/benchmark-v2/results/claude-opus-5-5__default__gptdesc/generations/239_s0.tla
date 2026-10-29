---- MODULE Countdown ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLE x

vars == <<x>>

Init == x = N

Next == \/ /\ x > 0
           /\ x' = x - 1
        \/ /\ x = 0
           /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == x >= 0

THEOREM Spec => []Inv
====