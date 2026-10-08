------------------------------ MODULE TwoPhaseCommit ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS RMs  \* The set of resource managers

VARIABLES rmStates  \* Mapping from each RM to its state: "working", "prepared", "committed", or "aborted"

Init == 
    /\ rmStates \in [RMs -> {"working"}]

Prepare(rm) ==
    /\ rm \in RMs
    /\ rmStates[rm] = "working"
    /\ rmStates' = [rmStates EXCEPT ![rm] = "prepared"]

Decide(commit, rm) ==
    /\ rm \in RMs
    /\ rmStates[rm] = "prepared"
    /\ commit \in {"commit", "abort"}
    /\ rmStates' = [rmStates EXCEPT ![rm] = commit]

Next == 
    \/ \E rm \in RMs : Prepare(rm)
    \/ \E rm \in RMs, commit \in {"commit", "abort"} : Decide(commit, rm)

Spec == 
    /\ Init
    /\ [][Next]_<<rmStates>>

TypeOk ==
    /\ rmStates \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Consistency ==
    \/ \A rm1, rm2 \in RMs : rmStates[rm1] = "aborted" \/ rmStates[rm2] = "aborted"
    \/ \A rm1, rm2 \in RMs : rmStates[rm1] = "committed" \/ rmStates[rm2] = "committed"

Properties ==
    /\ TypeOk
    /\ Consistency

THEOREM Spec => []Properties
=============================================================================