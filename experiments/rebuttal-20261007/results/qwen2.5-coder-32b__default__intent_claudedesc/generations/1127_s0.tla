------------------------------- MODULE AtomicCommit -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS RMSet  \* Set of resource managers

VARIABLES states \* State of each resource manager: "working", "prepared", "committed", or "aborted"

Init == /\ states \in [RMSet -> {"working"}]
        /\ Cardinality(RMSet) = 3

Next ==
    \/ \E rm \in RMSet : 
         /\ states[rm] = "working"
         /\ states' = [states EXCEPT ![rm] = "prepared"]
    \/ \E rm \in RMSet :
         /\ states[rm] = "working"
         /\ states' = [states EXCEPT ![rm] = "aborted"]
    \/ \A rm \in RMSet : 
         (\E r \in RMSet : states[r] = "prepared") => 
           (/\ states[rm] \in {"prepared", "committed", "aborted"}
            /\ states' = [states EXCEPT ![rm] = IF states[rm] = "prepared" THEN "committed" ELSE states[rm]])

Spec == Init /\ [][Next]_<<states>>

TypeCorrectness ==
    \A rm \in RMSet : states[rm] \in {"working", "prepared", "committed", "aborted"}

Consistency ==
    \/ (\E rm \in RMSet : states[rm] = "committed") => (\A r \in RMSet : states[r] \notin {"aborted"})
    \/ (\E rm \in RMSet : states[rm] = "aborted")  => (\A r \in RMSet : states[r] \notin {"committed"})

Invariant == TypeCorrectness /\ Consistency

=============================================================================