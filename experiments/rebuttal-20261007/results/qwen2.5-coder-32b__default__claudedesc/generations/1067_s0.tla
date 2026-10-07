------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES active, terminationDetected

Init == /\ active \in [0 .. N-1 -> BOOLEAN]
        /\ terminationDetected = FALSE \/ (\A i \in 0 .. N-1 : ~active[i])

Terminate(i) == /\ i \in 0 .. N-1
                /\ active[i]
                /\ active' = [active EXCEPT ![i] = FALSE]
                /\ (terminationDetected' = TRUE \/ terminationDetected')

Wakeup(i, j) == /\ i \in 0 .. N-1
               /\ j \in 0 .. N-1
               /\ active[i]
               /\ active' = [active EXCEPT ![j] = TRUE]
               /\ terminationDetected' = terminationDetected

DetectTermination == /\ (\A i \in 0 .. N-1 : ~active[i])
                     /\ terminationDetected'
                     /\ terminationDetected' = TRUE

Next == \/ (EXISTS i \in 0 .. N-1 : Terminate(i))
        \/ (EXISTS i, j \in 0 .. N-1 : Wakeup(i, j))
        \/ DetectTermination

Spec == Init /\ [][Next]_<<active, terminationDetected>> /\ WF_(DetectTermination)_

TDCorrect == [](terminationDetected => (\A i \in 0 .. N-1 : ~active[i]))

Quiescence == <>(\A i \in 0 .. N-1 : ~active[i]) /\ []<>(\A i \in 0 .. N-1 : ~active[i])

Liveness == <>(terminationDetected)

=============================================================================