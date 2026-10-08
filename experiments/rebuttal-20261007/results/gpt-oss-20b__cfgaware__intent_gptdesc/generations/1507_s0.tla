------------------------------ MODULE ClockBit ------------------------------
EXTENDS Naturals, TLC

VARIABLE b

Init == /\ b \in BOOLEAN
Next == /\ b' = ~b

TypeOK == b \in BOOLEAN

Assumption == b = ~~b

Spec == Init /\ [][Next]_<<b>> /\ []TypeOK

ASSUME Assumption

=============================================================================