---- MODULE Countdown ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLE x

vars == <<x>>

Init == x = N

Decrement == x > 0 /\ x' = x - 1

Stutter == x = 0 /\ UNCHANGED x

Next == Decrement \/ Stutter

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Inv == x >= 0

THEOREM Spec => []Inv
====