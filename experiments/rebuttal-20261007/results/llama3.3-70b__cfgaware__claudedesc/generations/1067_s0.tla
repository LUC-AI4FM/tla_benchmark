---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE active, terminationDetected

Init == (* Initial condition *)
        /\ active \in [0..N-1 -> BOOLEAN]
        /\ terminationDetected \in {TRUE, FALSE}

Terminate(i) == (* Deactivate a node and detect termination if all nodes are inactive *)
                /\ i \in 0..N-1
                /\ active' = [active EXCEPT ![i] = FALSE]
                /\ IF \A j \in 0..N-1 : ~active'[j] THEN terminationDetected' = TRUE ELSE terminationDetected' = terminationDetected

Wakeup(i, j) == (* Reactivate a node *)
                 /\ i \in 0..N-1
                 /\ active[i]
                 /\ j \in 0..N-1
                 /\ active' = [active EXCEPT ![j] = TRUE]
                 /\ terminationDetected' = terminationDetected

DetectTermination == (* Detect global termination *)
                      /\ \A i \in 0..N-1 : ~active[i]
                      /\ terminationDetected' = TRUE
                      /\ active' = active

Next == \E i \in 0..N-1 : Terminate(i) \/ \E i, j \in 0..N-1 : Wakeup(i, j) \/ DetectTermination

Spec == Init /\ [][Next]_<<active, terminationDetected>> /\ WF_DetectTermination(DetectTermination)

TDCorrect == []~(terminationDetected /\ \E i \in 0..N-1 : active[i])

Quiescence == [](\A i \in 0..N-1 : ~active[i] => []\A j \in 0..N-1 : ~active'[j])

Liveness == []<>terminationDetected

THEOREM Spec => []TDCorrect
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
====================================================================================