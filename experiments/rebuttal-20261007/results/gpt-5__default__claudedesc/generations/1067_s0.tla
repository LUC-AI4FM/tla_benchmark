----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES active, terminationDetected

Nodes == 0..(N - 1)

AllInactiveOf(ac) == \A i \in Nodes: ac[i] = FALSE
AllInactive == AllInactiveOf(active)

TypeOK == /\ active \in [Nodes -> BOOLEAN]
          /\ terminationDetected \in BOOLEAN

TDCorrect == terminationDetected => AllInactive

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN
  /\ terminationDetected => AllInactive

Terminate(i) ==
  LET newActive == [active EXCEPT ![i] = FALSE]
  IN /\ i \in Nodes
     /\ active[i] = TRUE
     /\ active' = newActive
     /\ IF AllInactiveOf(newActive)
           THEN terminationDetected' \in {terminationDetected, TRUE}
           ELSE terminationDetected' = terminationDetected

Wakeup(i, j) ==
  /\ i \in Nodes
  /\ j \in Nodes
  /\ active[i] = TRUE
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ terminationDetected' = terminationDetected

DetectTermination ==
  /\ AllInactive
  /\ ~terminationDetected
  /\ active' = active
  /\ terminationDetected' = TRUE

Stutter ==
  /\ active' = active
  /\ terminationDetected' = terminationDetected

Next ==
  \/ (\E i \in Nodes: Terminate(i))
  \/ (\E i \in Nodes: \E j \in Nodes: Wakeup(i, j))
  \/ DetectTermination
  \/ Stutter

Vars == << active, terminationDetected >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(DetectTermination)

Quiescence == [](AllInactive => []AllInactive)

Liveness == [](AllInactive => <> terminationDetected)

===========================================================================================