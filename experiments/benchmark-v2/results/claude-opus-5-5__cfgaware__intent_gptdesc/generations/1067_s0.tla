------------------------- MODULE SyncTerminationDetection -------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1

VARIABLES active, terminationDetected

vars == << active, terminationDetected >>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A i \in Nodes : ~ active[i]

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

Wakeup(i, j) ==
  /\ active[i]
  /\ j # i
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ ~ terminationDetected
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

Done ==
  /\ terminated
  /\ terminationDetected
  /\ UNCHANGED vars

Next ==
  \/ \E i \in Nodes : Terminate(i)
  \/ \E i \in Nodes : \E j \in Nodes : Wakeup(i, j)
  \/ DetectTermination
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

TDCorrect == terminationDetected => terminated

Quiescence == [](terminated => []terminated)

Liveness == terminated ~> terminationDetected

=============================================================================