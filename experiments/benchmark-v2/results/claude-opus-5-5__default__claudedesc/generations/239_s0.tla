---- MODULE Test1623 ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLE x

vars == << x >>

Init == x = N

Decrement == /\ x > 0
             /\ x' = x - 1

Stay == /\ x = 0
        /\ x' = x

Next == Decrement \/ Stay

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Inv == x >= 0

====