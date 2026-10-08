------------------------------ MODULE InitializationPattern ------------------------------

EXTENDS Integers, TLC

CONSTANTS Init

VARIABLES s

Init == \/ s = 0

Next == UNCHANGED s

Spec == /\ Init
        /\ []Inv
        /\ []<Next>_s

Inv == s < 1

================================================================================