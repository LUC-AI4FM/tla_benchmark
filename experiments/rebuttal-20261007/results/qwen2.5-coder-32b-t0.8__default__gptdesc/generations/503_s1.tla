------------------------------ MODULE Consensus ------------------------------

EXTENDS TLC, FiniteSets

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Next ==
  \/ /\ chosen = {}
     /\ \E v \in Values : chosen' = {v}
  \/ /\ chosen /= {}
     /\ chosen' = chosen

Spec ==
  Init /\ [][Next]_<<chosen>>

TypeOK ==
  /\ chosen \subseteq Values
  /\ Cardinality(chosen) <= 1

Safety == []TypeOK

Liveness == <>[](\E v \in Values : chosen = {v})

WF == WF_next(<<chosen>>)

=============================================================================