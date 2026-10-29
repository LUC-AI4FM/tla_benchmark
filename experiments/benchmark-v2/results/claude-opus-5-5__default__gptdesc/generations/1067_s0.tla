---- MODULE SyncTerminationDetection ----
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES active, terminationDetected

vars == <<active, terminationDetected>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED terminationDetected

Wakeup(i, j) ==
  /\ active[i]
  /\ ~ active[j]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ ~ terminationDetected
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E i \in Node : Terminate(i)
  \/ \E i, j \in Node : Wakeup(i, j)
  \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

TDCorrect == terminationDetected => terminated

Quiescence == [](terminated => []terminated)

Liveness == terminated ~> terminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => []TDCorrect
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
====