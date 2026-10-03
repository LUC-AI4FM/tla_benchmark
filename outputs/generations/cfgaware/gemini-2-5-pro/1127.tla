---- MODULE TwoPhaseCommit ----
EXTENDS TLC

CONSTANTS RM, r2

ASSUME r2 \in RM

VARIABLES rmState

vars == <<rmState>>

States == {"working", "prepared", "committed", "aborted"}

\* All resource managers start in the "working" state.
Init == rmState = [r \in RM |-> "working"]

\* An RM in the "working" state can move to the "prepared" state.
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

\* An RM can decide to commit if it is prepared and no other RM has aborted.
DecideCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ \A other \in RM : rmState[other] /= "aborted"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

\* An RM can decide to abort if it is prepared and no other RM has committed.
DecideAbort(r) ==
    /\ rmState[r] = "prepared"
    /\ \A other \in RM : rmState[other] /= "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

\* An RM can decide to commit or abort, subject to consistency constraints.
Decide(r) == DecideCommit(r) \/ DecideAbort(r)

\* The next state is determined by one RM taking one of the possible actions.
Next == \E r \in RM : Prepare(r) \/ Decide(r)

\* The main specification.
TCSpec == Init /\ [][Next]_vars

\* Type invariant: The state of each RM is always one of the allowed states.
TCTypeOK == \A r \in RM : rmState[r] \in States

\* Consistency invariant: It is never the case that one RM is committed while
\* another is aborted.
TCConsistent == ~(\E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted")

=============================================================================