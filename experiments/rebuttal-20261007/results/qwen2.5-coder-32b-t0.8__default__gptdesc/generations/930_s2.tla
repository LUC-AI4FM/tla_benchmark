------------------------------ MODULE Clock ------------------------------

EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple model

VARIABLES hr

Init == /\ hr \in 1..12

HCnxt == \/ hr < 12 -> hr' = hr + 1
         \/ hr = 12 -> hr' = 1

Next == HCnxt

Spec == Init /\ [][Next]_<<hr>>

HC == Spec /\ [](hr \in 1..12)

=============================================================================