------------------------------ MODULE TrivialStuttering ------------------------------

EXTENDS Integers

CONSTANTS DummyConst \* Unused placeholder to satisfy CONSTANTS section

VARIABLES x, y

vars == << x, y >>

Init ==
    /\ x = 0
    /\ y = 0
    /\ x = y

Next ==
    UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars

=============================================================================