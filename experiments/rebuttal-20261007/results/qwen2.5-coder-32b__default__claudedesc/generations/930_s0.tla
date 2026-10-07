------------------------------- MODULE HC -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple clock model

VARIABLES hr

HCini == 1 <= hr /\ hr <= 12

HCnxt == \/ hr' = (hr % 12) + 1
         \/ hr' = hr

Init == HCini

Next == HCnxt

Spec == Init /\ [][Next]_<<hr>>

THEOREM Spec => []HCini
=============================================================================