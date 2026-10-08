---- MODULE TerminationDetectionRing ----
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES active, detected

Node == 0..(N - 1)

Vars == << active, detected >>

AllInactive == \A i \in Node: ~active[i]

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ detected \in BOOLEAN
  /\ detected => AllInactive

Deactivate(i) ==
  /\ i \in Node
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED detected

Wake(i, j) ==
  /\ i \in Node
  /\ j \in Node
  /\ i # j
  /\ active[i]
  /\ ~active[j]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED detected

Detect ==
  /\ AllInactive
  /\ ~detected
  /\ detected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ Detect
  \/ \E i \in Node: Deactivate(i)
  \/ \E i \in Node: \E j \in Node: Wake(i, j)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Detect)

TypeInvariant ==
  /\ active \in [Node -> BOOLEAN]
  /\ detected \in BOOLEAN

NoFalseDetection ==
  [](detected => AllInactive)

TerminationStability ==
  [](AllInactive => []AllInactive)

TerminationLiveness ==
  [](AllInactive => <>detected)
====