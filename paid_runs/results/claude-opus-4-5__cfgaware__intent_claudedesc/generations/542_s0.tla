---------------------------- MODULE specification ----------------------------

EXTENDS Integers

VARIABLES x, pc1, pc2

vars == <<x, pc1, pc2>>

Init ==
    /\ x = 0
    /\ pc1 = "ready"
    /\ pc2 = "ready"

Increment1 ==
    /\ pc1 = "ready"
    /\ x' = x + 1
    /\ pc1' = "done"
    /\ pc2' = pc2

Increment2 ==
    /\ pc2 = "ready"
    /\ x' = x + 1
    /\ pc2' = "done"
    /\ pc1' = pc1

Next ==
    \/ Increment1
    \/ Increment2

Termination ==
    /\ pc1 = "done"
    /\ pc2 = "done"
    /\ UNCHANGED vars

Fairness ==
    /\ WF_vars(Increment1)
    /\ WF_vars(Increment2)

Spec ==
    /\ Init
    /\ [][Next \/ Termination]_vars
    /\ Fairness

=============================================================================