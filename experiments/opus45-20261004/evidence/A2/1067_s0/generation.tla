---------------------------- MODULE SyncTerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

Nodes == 0 .. N-1

Terminated == \A i \in Nodes : ~active[i]

TypeOK == /\ active \in [Nodes -> BOOLEAN]
          /\ terminationDetected \in BOOLEAN

Init == /\ active \in [Nodes -> BOOLEAN]
        /\ terminationDetected \in {FALSE, Terminated}

Terminate(i) == /\ active[i]
                /\ active' = [active EXCEPT ![i] = FALSE]
                /\ terminationDetected' \in {terminationDetected, 
                                              \A j \in Nodes : ~active'[j]}

Wakeup(i, j) == /\ active[i]
                /\ active' = [active EXCEPT ![j] = TRUE]
                /\ terminationDetected' = terminationDetected

DetectTermination == /\ Terminated
                     /\ terminationDetected' = TRUE
                     /\ active' = active

Next == \/ \E i \in Nodes : Terminate(i)
        \/ \E i, j \in Nodes : Wakeup(i, j)
        \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

TDCorrect == terminationDetected => Terminated

Quiescence == Terminated => [][Terminated]_vars

Liveness == Terminated ~> terminationDetected

=============================================================================