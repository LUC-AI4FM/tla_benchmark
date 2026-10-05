-------------------------------- MODULE AtomicCommit --------------------------------
EXTENDS Sequences, FiniteSets

CONSTANTS RM, r2

VARIABLES rmState

vars == <<rmState>>

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent == ~(\E rm1 \in RM : \E rm2 \in RM : 
                    rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm) == /\ rmState[rm] = "prepared"
              /\ \/ /\ canCommit
                    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
                 \/ /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

Abort(rm) == /\ rmState[rm] = "working"
             /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

Init == rmState = [rm \in RM |-> "working"]

Next == \E rm \in RM : Prepare(rm) \/ Decide(rm) \/ Abort(rm)

TCSpec == Init /\ [][Next]_vars

=============================================================================