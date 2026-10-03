----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals

CONSTANTS Node, Succ

ASSUME Node /= {} /\ Succ \in [Node -> Node]

VARIABLES active, detected

vars == << active, detected >>

AllInactive == \A n \in Node: ~active[n]

TypeInv == active \in [Node -> BOOLEAN] /\ detected \in BOOLEAN

CorrectnessInv == detected => AllInactive

Init ==
  /\ TypeInv
  /\ detected = FALSE

Terminate(n) ==
  /\ n \in Node
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED detected

Wake(n) ==
  /\ n \in Node
  /\ active[n]
  /\ LET m == Succ[n] IN active' = [active EXCEPT ![m] = TRUE]
  /\ UNCHANGED detected

Detect ==
  /\ ~detected
  /\ AllInactive
  /\ detected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E n \in Node: Terminate(n)
  \/ \E n \in Node: Wake(n)
  \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)

Quiescence == [](detected => UNCHANGED vars)

Liveness == (<>[] AllInactive) => <> detected

THEOREM Spec => []TypeInv

THEOREM Spec => []CorrectnessInv

THEOREM Spec => Quiescence

THEOREM Spec => Liveness

================================================================================