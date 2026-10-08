------------------------------- MODULE AsyncTerminationDetection -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES active, pendingMessages, globalTerminationDetected

Init == 
    /\ active \in [1..N -> BOOLEAN]
    /\ pendingMessages \in [1..N -> NATURAL]
    /\ globalTerminationDetected = FALSE
    /\ (\A i \in 1..N : active[i] \/ pendingMessages[i] > 0)

Next ==
    \/ \E i \in 1..N : 
        \/ \/ active[i] 
            /\ ~active'[i] 
            /\ pendingMessages'[i] = pendingMessages[i]
           \/ pendingMessages[i] > 0
              /\ pendingMessages'[i] < pendingMessages[i]
              /\ active'[i] = active[i]
    \/ globalTerminationDetected
       /\ globalTerminationDetected' = TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<active, pendingMessages, globalTerminationDetected>>

Invariant1 == 
    \A i \in 1..N : ~active[i] => pendingMessages[i] = 0

Invariant2 == 
    \/ ~globalTerminationDetected
    \/ (\A i \in 1..N : ~active[i] /\ pendingMessages[i] = 0)

Invariant3 ==
    [](globalTerminationDetected => []<>(~(pendingMessages'[_] # pendingMessages[_]) \/ ~(active'[_] # active[_])))

Fairness == 
    WF_<<active, pendingMessages, globalTerminationDetected>>(DetectTermination)

DetectTermination ==
    /\ \A i \in 1..N : ~active[i] /\ pendingMessages[i] = 0
    /\ ~globalTerminationDetected

=============================================================================