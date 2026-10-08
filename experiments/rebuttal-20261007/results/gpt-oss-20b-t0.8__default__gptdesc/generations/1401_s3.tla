MODULE Counter

EXTENDS Naturals, TLC

VARIABLE outerX

Init == outerX = 0

Enabled == outerX < 3

InnerStep == 
    /\ Enabled
    /\ outerX' = outerX + 1

Stutter == UNCHANGED <<outerX>>

Next == InnerStep \/ Stutter

Invariant == outerX <= 3

Spec == Init
        /\ [][Next]_<<outerX>>
        /\ WF_InnerStep
        /\ <> (outerX = 3)
        /\ Invariant