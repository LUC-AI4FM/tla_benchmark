---------------------------- MODULE TwoPhaseCommit ----------------------------

CONSTANT RM

VARIABLES rmState

r1 == "r1"
r2 == "r2"
r3 == "r3"

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent == ~(\E rm1 \in RM : \E rm2 \in RM : 
                    rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

TCInit == rmState = [rm \in RM |-> "working"]

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

notCommitted == ~(\E rm \in RM : rmState[rm] = "committed")

Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm) == \/ /\ rmState[rm] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
              \/ /\ rmState[rm] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)

TCSpec == TCInit /\ [][TCNext]_rmState

=============================================================================