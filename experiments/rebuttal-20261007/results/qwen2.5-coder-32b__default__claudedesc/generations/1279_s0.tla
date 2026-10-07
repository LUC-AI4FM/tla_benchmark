------------------------------- MODULE SimpleSystem -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES s

Init == s = 23

Next(var) == /\ var' \in {0, 1}
             /\ var' > var

Spec == Init /\ [][Next(s) \/ s' = s]_<<s>>

Inv == s /= 0
=============================================================================