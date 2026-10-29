---------------------------- MODULE PrimedFilter ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Domain == 0..1

Init == x = {}

Next == \E v \in Domain : /\ x' = v
                          /\ x' > 0

Spec == Init /\ [][Next]_vars

TypeOK == x \in {{}} \cup Domain

=============================================================================