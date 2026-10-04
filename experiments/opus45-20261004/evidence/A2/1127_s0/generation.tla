---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Sequences, FiniteSets

CONSTANTS RM

VARIABLES rmState

vars == <<rmState>>

TypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCTypeOK == TypeOK

TCConsistent == \A rm1, rm2 \in RM : 
    ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

notCommitted == \A rm \in RM : rmState[rm] # "committed"

Prepare(rm) == 
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm) == 
    \/ /\ rmState[rm] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    \/ /\ rmState[rm] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)

TCInit == rmState = [rm \in RM |-> "working"]

TCSpec == TCInit /\ [][TCNext]_vars

=============================================================================