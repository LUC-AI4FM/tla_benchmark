---- MODULE TCommitCompanion ----
EXTENDS TLAPlus

CONSTANTS RMs  \* Set of resource managers

VARIABLES rmState  \* State of each resource manager

Init == TRUE  \* No initial condition specified, just a placeholder

Next == TRUE  \* No next state action specified, just a placeholder

TypeCorrectness ==
    /\ \A rm \in RMs : rmState[rm] \in {"active", "prepared", "committed", "aborted"}

Consistency ==
    /\ ~(\E rm1, rm2 \in RMs : rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

Spec == Init /\ [][Next]_<<rmState>> /\ TypeCorrectness /\ Consistency
========================================