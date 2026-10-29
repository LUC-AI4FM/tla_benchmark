---- MODULE Countdown ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLE x

vars == <<x>>

Init == x = N

Next == IF x > 0
          THEN x' = x - 1
          ELSE UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Inv == x >= 0

THEOREM Spec => []Inv
====