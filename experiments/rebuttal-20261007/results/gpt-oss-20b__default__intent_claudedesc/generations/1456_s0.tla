MODULE SubsetSpec
EXTENDS SETS

CONSTANTS U1, U2, U3

UNIVERSE == {U1,U2,U3}
INIT_SET == {U1,U2}

VARIABLES S, T

Init ==
  /\ S \in SUBSET(INIT_SET)
  /\ T = UNIVERSE

Next ==
  /\ T' = T
  /\ S' \in SUBSET(T)

FullSetCount == _POSSIBLE [S' = UNIVERSE]
NewGainCount == _POSSIBLE [U3 \in S' /\ U3 \notin S]

Invariant ==
  /\ S \subseteq UNIVERSE
  /\ ENABLED (S' \subseteq {U1})
  /\ FullSetCount = 1
  /\ IF U3 \in S THEN NewGainCount = 0 ELSE NewGainCount = 4
  /\ T = UNIVERSE

Spec == Init /\ [][Next]_<<S,T>> /\ []Invariant