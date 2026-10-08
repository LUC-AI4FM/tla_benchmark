------------------------------- MODULE Consensus -------------------------------
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

\* Safety property: at most one value is ever chosen
TypeOK == chosen \subseteq Values \/ chosen = {}

\* Liveness property: eventually some value is chosen
ChosenEventually == <>[] (\E v \in Values : chosen = {v})

=============================================================================