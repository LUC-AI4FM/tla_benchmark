---------------------------- MODULE SyncTerminationDetection ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

Node == 0 .. N-1

Terminated == \A i \in Node : ~active[i]

Init == 
    /\ active \in [Node -> BOOLEAN]
    /\ terminationDetected \in {FALSE, Terminated}

Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ terminationDetected' \in {terminationDetected, \A j \in Node : ~active'[j]}

Wakeup(i, j) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
    /\ Terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E i \in Node : Terminate(i)
    \/ \E i, j \in Node : Wakeup(i, j)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

TDCorrect == terminationDetected => Terminated

Quiescence == Terminated => []Terminated

Liveness == Terminated ~> terminationDetected

=============================================================================