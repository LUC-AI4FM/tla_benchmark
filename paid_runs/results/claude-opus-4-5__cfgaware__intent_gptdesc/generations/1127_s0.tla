---------------------------- MODULE TwoPhaseCommit ----------------------------
CONSTANT RM

VARIABLES rmState

r2 == CHOOSE r \in RM : TRUE

vars == <<rmState>>

RMStates == {"working", "prepared", "committed", "aborted"}

TCTypeOK == rmState \in [RM -> RMStates]

TCConsistent == ~(\E r1 \in RM : \E r2_local \in RM : 
                    rmState[r1] = "committed" /\ rmState[r2_local] = "aborted")

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] /= "committed"

Prepare(r) == 
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
    /\ rmState[r] = "prepared"
    /\ canCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ notCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Init == rmState = [r \in RM |-> "working"]

Next == \E r \in RM : Prepare(r) \/ Decide(r) \/ Abort(r)

TCSpec == Init /\ [][Next]_vars

AllPreparedCanCommit == 
    (\A r \in RM : rmState[r] = "prepared") => 
    (\A r \in RM : ENABLED Decide(r))

THEOREM TCSpec => []TCTypeOK

THEOREM TCSpec => []TCConsistent

=============================================================================