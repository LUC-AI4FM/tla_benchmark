---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Sequences, FiniteSets

CONSTANT RM

VARIABLE rmState

r2 == CHOOSE r \in RM : TRUE

vars == <<rmState>>

TypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCTypeOK == TypeOK

TCConsistent ==
    \A rm1, rm2 \in RM : ~ (rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

canCommit ==
    \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

canAbort ==
    \A rm \in RM : rmState[rm] # "committed"

Prepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm) ==
    \/ /\ rmState[rm] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    \/ /\ rmState[rm] \in {"working", "prepared"}
       /\ canAbort
       /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

Init ==
    rmState = [rm \in RM |-> "working"]

Next ==
    \E rm \in RM : Prepare(rm) \/ Decide(rm)

Spec == Init /\ [][Next]_vars

TCSpec == Spec /\ []TCTypeOK /\ []TCConsistent

THEOREM Spec => []TCTypeOK
THEOREM Spec => []TCConsistent

=============================================================================