------------------------------- MODULE TrivialStuttering -------------------------------

EXTENDS Naturals

VARIABLES x, y

Init ==
    /\ x = 0
    /\ y = 0
    /\ x = y

Next ==
    UNCHANGED <<x, y>>

Spec ==
    Init /\ [][Next]_<<x, y>>

============================================================================