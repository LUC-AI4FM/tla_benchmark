------------------------------- MODULE TerminationDetection ------------------------------

CONSTANTS N \* Number of nodes

VARIABLES active, pendingMessages, terminated

\* Set of all node identifiers
NodeSet == 1..N

\* Initial predicate: Nodes can start in any mix of active and inactive states with no pending messages.
Init == /\ active \in [NodeSet -> BOOLEAN]
        /\ pendingMessages \in [NodeSet -> NATURAL]
        /\ terminated = FALSE
        /\ (\A n \in NodeSet : pendingMessages[n] = 0) => terminated \in {TRUE, FALSE}

\* Next-state relation: Nodes can send messages, deactivate, and reactivate.
Next == \/ \E sender \in NodeSet, receiver \in NodeSet, sender # receiver :
            /\ active[sender]
            /\ pendingMessages' = [pendingMessages EXCEPT ![receiver] = pendingMessages[receiver] + 1]
            /\ UNCHANGED <<active, terminated>>
        \/ \E n \in NodeSet :
            /\ active[n]
            /\ active' = [active EXCEPT ![n] = FALSE]
            /\ UNCHANGED <<pendingMessages, terminated>>
        \/ \E n \in NodeSet :
            /\ pendingMessages[n] > 0
            /\ active'[n] = TRUE
            /\ pendingMessages'[n] = pendingMessages[n] - 1
            /\ UNCHANGED <<active, terminated>>

\* Termination detection: The system is considered terminated if all nodes are inactive and have no pending messages.
SpecTermination == \A n \in NodeSet : ~active[n] /\ pendingMessages[n] = 0

\* Safety property: The termination flag can only be set when the system has genuinely terminated.
Safety == [](terminated => SpecTermination)

\* Quiescence property: Once terminated, the system cannot become un-terminated.
Quiescence == <>[](SpecTermination => []<>terminated)

\* Liveness property: If the system terminates, the termination flag will eventually be set.
Liveness == <>(SpecTermination => <>terminated)

\* Full specification
Spec == Init /\ [][Next]_<<active, pendingMessages, terminated>> /\ Safety /\ Quiescence /\ Liveness

=============================================================================