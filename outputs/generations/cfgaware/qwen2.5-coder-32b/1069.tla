------------------------------- MODULE AsyncTermDetection ------------------------------

CONSTANTS N \* Number of nodes

VARIABLES active, pendingMessages, globalTerminationDetected

\* active[i] is TRUE if node i is active, FALSE otherwise
\* pendingMessages[i] is the count of pending messages at node i
\* globalTerminationDetected is TRUE if termination has been detected globally, FALSE otherwise

Init == /\ active = [i \in 1..N -> TRUE]
        /\ pendingMessages = [i \in 1..N -> 0]
        /\ globalTerminationDetected = FALSE

NodeTerminates(i) ==
    /\ active[i]
    /\ pendingMessages[i] = 0
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pendingMessages, globalTerminationDetected>>

SendMessage(from, to) ==
    /\ active[from]
    /\ pendingMessages[to] < N \* Assuming a bound on the number of messages for bounded model checking
    /\ pendingMessages' = [pendingMessages EXCEPT ![to] = pendingMessages[to] + 1]
    /\ UNCHANGED <<active, globalTerminationDetected>>

ReceiveMessage(i) ==
    /\ active[i]
    /\ pendingMessages[i] > 0
    /\ pendingMessages' = [pendingMessages EXCEPT ![i] = pendingMessages[i] - 1]
    /\ UNCHANGED <<active, globalTerminationDetected>>

DetectTermination ==
    /\ ~globalTerminationDetected
    /\ \A i \in 1..N : ~active[i] /\ pendingMessages[i] = 0
    /\ globalTerminationDetected' = TRUE
    /\ UNCHANGED <<active, pendingMessages>>

Next == \/ \E i \in 1..N : NodeTerminates(i)
        \/ \E from, to \in 1..N : SendMessage(from, to)
        \/ \E i \in 1..N : ReceiveMessage(i)
        \/ DetectTermination

Spec == Init /\ [][Next]_<<active, pendingMessages, globalTerminationDetected>>

\* Invariants
InvActivePending ==
    \A i \in 1..N : ~active[i] => pendingMessages[i] = 0

InvGlobalTerminationStable ==
    \/ ~globalTerminationDetected
    \/ []<>(~[]<>globalTerminationDetected)

\* Liveness properties
SpecLiveness ==
    Spec /\ InvActivePending /\ InvGlobalTerminationStable
          /\ <>(globalTerminationDetected)

=============================================================================