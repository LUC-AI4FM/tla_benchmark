------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES activeNodes, terminationDetected

Init == /\ activeNodes \in SUBSET (1..N)
        /\ terminationDetected = (activeNodes = {})

Next ==
    \/ /\ CHOOSE node \in activeNodes: TRUE
       /\ activeNodes' = activeNodes \ {node}
       /\ UNCHANGED terminationDetected
    \/ /\ CHOOSE node \notin activeNodes, otherNode \in activeNodes: TRUE
       /\ activeNodes' = activeNodes \cup {node}
       /\ UNCHANGED terminationDetected
    \/ /\ (activeNodes = {})
       /\ terminationDetected'
       /\ UNCHANGED activeNodes

Spec ==
    /\ Init
    /\ [][Next]_<<activeNodes, terminationDetected>>
    /\ WF_next(<<activeNodes, terminationDetected>>, {s \in S: s.terminationDetected = FALSE})

TerminationNotFalselyReported == [](terminationDetected => (activeNodes = {}))

StableTermination ==
    \/ (activeNodes = {})
    \/ [](activeNodes' = activeNodes)

Liveness ==
    <>(terminationDetected)

THEOREM Spec => []TerminationNotFalselyReported
THEOREM Spec => StableTermination
THEOREM Spec => Liveness

=============================================================================