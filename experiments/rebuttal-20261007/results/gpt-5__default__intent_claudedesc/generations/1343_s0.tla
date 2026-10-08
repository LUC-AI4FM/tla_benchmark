------------------------------ MODULE ConjInitSimultaneous ------------------------------

EXTENDS Integers

VARIABLES x, y

vars == << x, y >>

Init ==
    /\ y = 0
    /\ x = 0
    /\ y = x

Next ==
    UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars

Inv ==
    x = 0 /\ y = 0

Safety ==
    []Inv

DoNothing ==
    [][Next]_vars

=============================================================================