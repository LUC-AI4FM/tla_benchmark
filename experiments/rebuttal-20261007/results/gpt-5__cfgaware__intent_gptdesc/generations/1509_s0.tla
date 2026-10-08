--------------------------- MODULE FiniteStateMap ---------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Dom

ASSUME IsFiniteSet(Dom) /\ Cardinality(Dom) >= 3

VARIABLES st, map

Val == 1..5

TypeInv ==
  /\ st \in Val
  /\ map \in [Dom -> Val]

CoverInv ==
  \E i \in Dom: map[i] = st

Inv == TypeInv /\ CoverInv

Init ==
  /\ st \in Val
  /\ map \in [Dom -> Val]
  /\ \E i \in Dom: map[i] = st

Next ==
  /\ st' \in Val
  /\ map' \in [Dom -> Val]
  /\ \E i \in Dom: map'[i] = st'

vars == << st, map >>

Spec == Init /\ [][Next]_vars

Liveness == [](ENABLED Next)

THEOREM Spec => []Inv

=============================================================================