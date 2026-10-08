------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS RMs  \* Set of resource managers

VARIABLES states  \* States of each RM: "working", "prepared", "committed", "aborted"

Init == 
    /\ states \in [RMs -> {"working"}]

Prepare(r) ==
    \/ states[r] = "working"
    /\ states' = [states EXCEPT ![r] = "prepared"]

Decide(r, decision) ==
    \/ decision \in {"committed", "aborted"}
    \/ states[r] = "prepared"
    /\ states' = [states EXCEPT ![r] = decision]

Next ==
    \E r \in RMs : Prepare(r)
        \/ \E r \in RMs, d \in {"committed", "aborted"} : Decide(r, d)

Spec ==
    Init /\ [][Next]_<<states>>

TypeOK ==
    /\ states \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Safety ==
    \/ \A r1, r2 \in RMs : ~(states[r1] = "committed" /\ states[r2] = "aborted")

Consistency ==
    TypeOK /\ Safety

THEOREM Spec => []Consistency
=============================================================================