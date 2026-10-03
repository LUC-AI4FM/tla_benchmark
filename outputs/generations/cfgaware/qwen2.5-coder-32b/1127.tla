------------------------------- MODULE TwoPhaseCommit -------------------------------

CONSTANTS RM  \* The set of resource managers

VARIABLES state \* State of each RM, a function from RM to {"working", "prepared", "committed", "aborted"}

\* Define the initial predicate
Init == 
    /\ state \in [RM -> {"working"}]

\* Define the action for Prepare
Prepare(r) ==
    /\ state[r] = "working"
    /\ \/ state' = [state EXCEPT ![r] = "prepared"]
       \/ state' = [state EXCEPT ![r] = "aborted"]

\* Define the action for Decide
Decide(r, decision \in {"committed", "aborted"}) ==
    /\ state[r] = "prepared"
    /\ state' = [state EXCEPT ![r] = decision]

\* Define the next-state relation as the disjunction of all possible Prepare and Decide actions
Next == 
    \/ \E r \in RM : Prepare(r)
    \/ \E r \in RM, d \in {"committed", "aborted"} : Decide(r, d)

\* Define the specification
Spec == Init /\ [][Next]_<<state>>

\* Type correctness property: state is a function from RM to {"working", "prepared", "committed", "aborted"}
TCTypeOK ==
    /\ state \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* Consistency invariant: no two RMs can be in conflicting states
TCConsistent ==
    \/ ~(\E r1, r2 \in RM : state[r1] = "committed" /\ state[r2] = "aborted")
    \/ ~(\E r1, r2 \in RM : state[r1] = "aborted" /\ state[r2] = "committed")

\* Define the complete specification with invariants
TCSpec == Spec /\ WF_<<state>>(Next) /\ []TCTypeOK /\ []TCConsistent

=============================================================================