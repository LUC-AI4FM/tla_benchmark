```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES active, terminationDetected

Init ==
  /\ active \in [0..N-1 -> BOOLEAN]
  /\ terminationDetected \in {TRUE, FALSE}

Next ==
  \/ \E i \in 0..N-1 : Terminate(i)
  \/ \E i, j \in 0..N-1 : Wakeup(i, j)
  \/ DetectTermination

Terminate(i) ==
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' = IF \A k \in 0..N-1 : ~active[k] THEN TRUE ELSE terminationDetected
  /\ i \in 0..N-1
  /\ active[i]

Wakeup(i, j) ==
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ terminationDetected' = terminationDetected
  /\ i \in 0..N-1
  /\ j \in 0..N-1
  /\ active[i]

DetectTermination ==
  /\ terminationDetected' = IF \A k \in 0..N-1 : ~active[k] THEN TRUE ELSE terminationDetected
  /\ active' = active

Spec ==
  Init /\ [][Next]_<<active, terminationDetected>> /\ WF_(DetectTermination)()

TDCorrect == []<>(terminationDetected => \A k \in 0..N-1 : ~active[k])
Quiescence == [](\A k \in 0..N-1 : ~active[k] => []\A l \in 0..N-1 : ~active[l])
Liveness == []<>(\A k \in 0..N-1 : ~active[k]) => <>terminationDetected
```