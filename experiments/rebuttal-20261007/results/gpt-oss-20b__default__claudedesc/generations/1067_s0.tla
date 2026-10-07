------------------------------ MODULE TerminationDetection ------------------------------
EXTENDS Integers

CONSTANTS N

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

Init ==
    /\ active \in [0 .. N-1 -> BOOLEAN]
    /\ terminationDetected \in BOOLEAN
    /\ (terminationDetected = FALSE \/ 
        (terminationDetected = TRUE /\ ~Exists i \in 0 .. N-1 : active[i]))

Terminate(i) ==
    /\ i \in 0 .. N-1
    /\ active[i] = TRUE
    /\ LET newActive == [active EXCEPT ![i] = FALSE]
       IN
          \/ (active' = newActive /\ terminationDetected' = terminationDetected)
          \/ (active' = newActive /\ terminationDetected' = TRUE 
              /\ ~Exists k \in 0 .. N-1 : newActive[k])

Wakeup(i, j) ==
    /\ i \in 0 .. N-1
    /\ j \in 0 .. N-1
    /\ active[i] = TRUE
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
    /\ ~Exists i \in 0 .. N-1 : active[i]
    /\ terminationDetected' = TRUE
    /\ active' = active

Next ==
    (\E i \in 0 .. N-1 : Terminate(i))
 \/ (\E i, j \in 0 .. N-1 : Wakeup(i,j))
 \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

TDCorrect == terminationDetected => ~Exists i \in 0 .. N-1 : active[i]

Quiescence ==
    [] ( (~Exists i \in 0 .. N-1 : active[i]) 
        => (~Exists i \in 0 .. N-1 : active'[i]))

Liveness == [](~Exists i \in 0 .. N-1 : active[i] => <> terminationDetected)

=============================================================================