---------------------------- MODULE TwoPhaseCommit ----------------------------
CONSTANT RM

VARIABLE rmState

r2 == CHOOSE r \in RM : TRUE

TypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCTypeOK == TypeOK

Consistent == 
    \A rm1, rm2 \in RM : ~(rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

TCConsistent == Consistent

Init == rmState = [rm \in RM |-> "working"]

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

canAbort == \E rm \in RM : rmState[rm] \in {"working", "aborted"}

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

Next == \E rm \in RM : Prepare(rm) \/ Decide(rm)

TCSpec == Init /\ [][Next]_rmState

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)

=============================================================================