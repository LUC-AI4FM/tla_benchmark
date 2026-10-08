MODULE TerminationDetection

EXTENDS Naturals, Sequences, TLC

CONSTANTS Node

VARIABLES active, detectionFlag

TypeInvariant == /\ active \in [Node -> BOOLEAN]
                /\ detectionFlag \in BOOLEAN

Init ==
  /\ TypeInvariant
  /\ active = [n \in Node |-> TRUE]
  /\ detectionFlag = FALSE

Terminate(n) ==
  /\ n \in Node
  /\ active[n] = TRUE
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ detectionFlag' = detectionFlag

WakeUp(m, n) ==
  /\ m \in Node
  /\ n \in Node
  /\ m # n
  /\ active[m] = TRUE
  /\ active[n] = FALSE
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ detectionFlag' = detectionFlag

Detect ==
  /\ detectionFlag = FALSE
  /\ (\A n \in Node : active[n] = FALSE)
  /\ detectionFlag' = TRUE
  /\ active' = active

Next == (∃ n \in Node : Terminate(n)) \/ (∃ m,n \in Node : WakeUp(m, n)) \/ Detect

Spec == Init /\ [][Next]_<<active, detectionFlag>> /\ WF_Detect

SafetyInvariant == detectionFlag => (\A n \in Node : active[n] = FALSE)

Quiescence == [] ((\A n \in Node : active[n] = FALSE) => <> detectionFlag)

Liveness == <> detectionFlag

END MODULE