---------------------------- MODULE AtomicCommit ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS RM

VARIABLES rmState

vars == <<rmState>>

RMStates == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> RMStates]

Consistency == \A r1, r2 \in RM : ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

AllPrepared == \A r \in RM : rmState[r] \in {"prepared", "committed"}

Init == rmState = [r \in RM |-> "working"]

Prepare(r) == 
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit(r) ==
    /\ rmState[r] = "prepared"
    /\ AllPrepared
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ \A rm \in RM : rmState[rm] # "committed"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next == \E r \in RM : Prepare(r) \/ Commit(r) \/ Abort(r)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK

THEOREM Spec => []Consistency

=============================================================================