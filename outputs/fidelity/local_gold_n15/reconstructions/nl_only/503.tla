---- MODULE SingleValueConsensus ----

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
  /\ Init
  /\ [][Next]_<<chosen>>
  /\ WF_next(Next)

THEOREM ChosenAtMostOneValue == 
  [](Cardinality(chosen) <= 1)

WF_next(action) ==
  \A S \in StateSpace : action(S) => \/ chosen' = chosen
                                      \/ \E v \in Values : chosen' = {v}
========================================