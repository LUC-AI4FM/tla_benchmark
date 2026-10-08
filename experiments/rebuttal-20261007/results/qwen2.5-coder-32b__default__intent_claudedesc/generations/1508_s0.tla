------------------------------- MODULE SimpleStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS MAX_VALUE

VARIABLES x

Init == x = 0

Next ==
    \/ x' = 5
    \/ x' \in {1, 2, 3}
    \/ x' = MAX_VALUE + 1
    \/ (x = 0 /\ x' = 1)
    \/ (x = 1 /\ x' = 2)

Invariants ==
    /\ x \in 0..MAX_VALUE
    /\ x = 0

Spec ==
    Init /\ [][Next]_<<x>> /\ Invariants

=============================================================================