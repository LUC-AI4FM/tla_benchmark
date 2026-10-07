---- MODULE TrivialStutter ----
EXTENDS TLC

CONSTANTS dummy

VARIABLES u1

vars == << u1 >>

Init == u1 = TRUE

Next ==
    /\ UNCHANGED vars
    /\ UNCHANGED << u1 >>
    /\ UNCHANGED u1

Prop == ENABLED Next

Spec == Init /\ [][Next]_vars

====