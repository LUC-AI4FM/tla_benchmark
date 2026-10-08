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

Spec ==
  /\ Init
  /\ [][Next]_<<chosen>>
  /\ WF_next(Next)

(* Invariants *)
ChosenBound == Cardinality(chosen) <= 1

(* Liveness *)
EventuallyChoose == <>[](\E v \in Values : chosen = {v})

=============================================================================