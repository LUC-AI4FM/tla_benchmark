------------------------------- MODULE TwoPhaseCommit -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS RMs  \* Set of resource managers

VARIABLES states  \* States of each RM: "working", "prepared", "committed", "aborted"

Init == 
    /\ states \in [RMs -> {"working"}]

Prepare(RM) ==
    /\ states[RM] = "working"
    /\ states' = [states EXCEPT ![RM] = "prepared"]

Decide(RM, decision) ==
    \/ /\ states[RM] = "prepared"
       /\ decision \in {"committed", "aborted"}
       /\ states' = [states EXCEPT ![RM] = decision]
    \/ /\ states[RM] \notin {"prepared"}
       /\ states' = states

Next == 
    \E RM \in RMs : \E decision \in {"committed", "aborted"} :
        Prepare(RM) \/ Decide(RM, decision)

Spec == 
    Init /\ [][Next]_<<states>>

TypeOK ==
    /\ states \in [RMs -> {"working", "prepared", "committed", "aborted"}]

Consistency ==
    LET committedRMs == {RM \in RMs : states[RM] = "committed"}
        abortedRMs  == {RM \in RMs : states[RM] = "aborted"}
    IN
        /\ committedRMs \cap abortedRMs = {}

Properties == 
    TypeOK /\ Consistency

THEOREM Spec => []Properties
=============================================================================