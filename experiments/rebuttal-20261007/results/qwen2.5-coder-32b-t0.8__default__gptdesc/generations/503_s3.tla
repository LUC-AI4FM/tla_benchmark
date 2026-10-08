------------------------------ MODULE Consensus ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Next ==
  \/ /\ chosen = {}
     /\ \E v \in Values : chosen' = {v}
  \/ /\ chosen /= {}
     /\ chosen' = chosen

Spec == Init /\ [][Next]_<<chosen>>

TypeOK == chosen \subseteq Values \/ chosen = {}

ChosenOnce ==
  \/ chosen = {}
  \/ (\E v \in Values : chosen = {v})

Safety == TypeOK /\ ChosenOnce

Live == <>[](chosen /= {})

WF == WF_next(Next, <<chosen>>)

SpecWithFairness == Spec /\ Live /\ WF

THEOREM Spec => []<>(TypeOK /\ ChosenOnce)

=============================================================================