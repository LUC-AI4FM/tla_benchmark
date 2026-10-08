------------------------------- MODULE AtomicCommit -------------------------------

CONSTANTS RM  \* Set of resource managers

VARIABLES state \* State of each resource manager

\* Define possible states for a resource manager
TYPEOK == /\ state \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* Ensure no conflicting decisions are made
CONSISTENT == ~(\E r1, r2 \in RM : state[r1] = "committed" /\ state[r2] = "aborted")

\* Initial predicate: all resource managers start in the working state
Init == state = [r \in RM |-> "working"]

\* Next-state relation for a single resource manager to prepare
Prepare(r) == 
    /\ state[r] = "working"
    /\ state' = [state EXCEPT ![r] = "prepared"]

\* Next-state relation for a single resource manager to abort
Abort(r) ==
    /\ state[r] \in {"working", "prepared"}
    /\ state' = [state EXCEPT ![r] = "aborted"]

\* Next-state relation for all resource managers to commit if all are prepared
Commit ==
    /\ (\A r \in RM : state[r] \in {"prepared", "committed"})
    /\ state' = [r \in RM |-> IF state[r] = "prepared" THEN "committed" ELSE state[r]]

\* Full next-state relation
Next == 
    \/ \E r \in RM : Prepare(r)
    \/ \E r \in RM : Abort(r)
    \/ Commit

\* Specification of the system
Spec == Init /\ [][Next]_<<state>>

\* Define the safety invariants
TCTypeOK == TYPEOK
TCConsistent == CONSISTENT

\* Full specification with invariants
TCSpec == Spec /\ []TCTypeOK /\ []TCConsistent

=============================================================================