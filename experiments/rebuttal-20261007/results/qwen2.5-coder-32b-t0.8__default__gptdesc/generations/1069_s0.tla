------------------------------- MODULE AsyncTermDetect -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES 
    active,         \* Set of currently active nodes
    pendingMessages,\* Pending messages count for each node
    globalTerminationDetected

Init == /\ active = {1..N}
        /\ pendingMessages = [node \in 1..N |-> 0]
        /\ globalTerminationDetected = FALSE

Next ==
    \/ /\ CHOOSE node \in active: 
            UNCHANGED <<active, pendingMessages EXCEPT ![node] = pendingMessages[node] + 1>, globalTerminationDetected>>
    \/ /\ CHOOSE node \notin active:
            /\ pendingMessages[node] > 0
            /\ /\ pendingMessages' = [pendingMessages EXCEPT ![node] = pendingMessages[node] - 1]
               /\ UNCHANGED <<active, globalTerminationDetected>>
    \/ /\ CHOOSE node \in active:
            /\ active' = active \ {node}
            /\ UNCHANGED <<pendingMessages, globalTerminationDetected>>
    \/ /\ CHOOSE node \notin active:
            /\ pendingMessages[node] = 0
            /\ active' = active \cup {node}
            /\ UNCHANGED <<pendingMessages, globalTerminationDetected>>
    \/ /\ globalTerminationDetected
        /\ UNCHANGED <<active, pendingMessages>>

Spec ==
    /\ Init
    /\ [][Next]_<<active, pendingMessages, globalTerminationDetected>>
    /\ WF_next(<<active, pendingMessages, globalTerminationDetected>>, {DetectTermination})

DetectTermination ==
    /\ globalTerminationDetected' = (active = {} /\ \A node \in 1..N: pendingMessages[node] = 0)
    /\ UNCHANGED <<active, pendingMessages>>

\* Safety properties
TerminationImpliesDetection == 
    G(\/ globalTerminationDetected => (\A node \in 1..N: pendingMessages[node] = 0) /\ active = {})

StableOnceReached ==
    [](globalTerminationDetected => []<>(/\ globalTerminationDetected
                                             /\ \A node \in 1..N: pendingMessages[node] = 0 
                                                /\ active = {}))

\* Liveness properties
ActualTerminationLeadsToDetection ==
    <>(\/ globalTerminationDetected => (\A node \in 1..N: pendingMessages[node] = 0) /\ active = {})

InvariantActiveSubsetNodes == 
    G(active \subseteq {1..N})

InvariantPendingNonNegative ==
    G(\A node \in 1..N: pendingMessages[node] >= 0)

StateConstraintForBoundedModelChecking ==
    \A node \in 1..N: pendingMessages[node] <= N

=============================================================================