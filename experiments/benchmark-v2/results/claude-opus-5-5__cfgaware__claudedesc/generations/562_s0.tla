---- MODULE TCommit ----
CONSTANT RM

VARIABLE rmState

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) == /\ rmState[r] = "prepared"
                   /\ canCommit
                   /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) == /\ rmState[r] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r)

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent == \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"
====