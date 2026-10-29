---- MODULE MCTCommit ----
EXTENDS TCommit

CONSTANTS RMs

VARIABLES dummy

\* Aliases for the behavior of TCommit (rmState and RM come from TCommit).
Init == TCInit /\ dummy = 0

Next == TCNext /\ UNCHANGED dummy

Spec == Init /\ [][Next]_<<rmState, dummy>>

\* Each resource manager is in one of the four named states.
TCTypeCorrect ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* No two resource managers can be in "aborted" and "committed" respectively.
TCConsistency ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

THEOREM Spec => [](TCTypeCorrect /\ TCConsistency)
====