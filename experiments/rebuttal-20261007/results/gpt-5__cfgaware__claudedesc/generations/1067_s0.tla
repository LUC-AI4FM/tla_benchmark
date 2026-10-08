------------------------------ MODULE TerminationDetection ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Nodes == 0..(N-1)

VARIABLES active, terminationDetected

vars == << active, terminationDetected >>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

AllInactive == \A i \in Nodes: ~active[i]

Init ==
  /\ TypeOK
  /\ (terminationDetected = FALSE
      \/ (terminationDetected = TRUE /\ AllInactive))

Terminate(i) ==
  /\ i \in Nodes
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' = IF AllInactive' THEN TRUE ELSE terminationDetected

Wakeup(i, j) ==
  /\ i \in Nodes /\ j \in Nodes
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ terminationDetected' = terminationDetected

DetectTermination ==
  /\ AllInactive
  /\ active' = active
  /\ terminationDetected' = TRUE

Next ==
  \/ (\E i \in Nodes: Terminate(i))
  \/ (\E i \in Nodes: \E j \in Nodes: Wakeup(i, j))
  \/ DetectTermination

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTermination)

TDCorrect ==
  terminationDetected => AllInactive

Quiescence ==
  [](AllInactive => []AllInactive)

Liveness ==
  (<>[] AllInactive) => <> terminationDetected

=============================================================================