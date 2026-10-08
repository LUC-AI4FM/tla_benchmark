------------------------------ MODULE MultiInstanceConsensus ------------------------------

EXTENDS FiniteSets

CONSTANTS Values, Slots

ASSUME /\ Values # {}
       /\ Slots # {}

VARIABLES proposals, chosen

vars == <<proposals, chosen>>

Init ==
  /\ proposals = {}
  /\ chosen = [s \in Slots |-> {}]

Propose ==
  \E v \in Values \ proposals :
    /\ proposals' = proposals \cup {v}
    /\ chosen' = chosen

Decide(s) ==
  /\ s \in Slots
  /\ chosen[s] = {}
  /\ proposals # {}
  /\ \E v \in proposals :
        /\ chosen' = [chosen EXCEPT ![s] = {v}]
        /\ proposals' = proposals

Next ==
  Propose \/ (\E s \in Slots : Decide(s))

Spec ==
  Init /\ [][Next]_vars

LiveSpec ==
  Spec /\ SF_vars(Propose) /\ \A s \in Slots : SF_vars(Decide(s))

(*
  State and temporal properties for verification
*)

TypeInv ==
  /\ proposals \subseteq Values
  /\ \A s \in Slots :
        /\ chosen[s] \subseteq Values
        /\ IsFiniteSet(chosen[s])
        /\ Cardinality(chosen[s]) \in {0, 1}

Safety_ChosenFromProposed ==
  \A s \in Slots : chosen[s] \subseteq proposals

Safety_UniquePerSlot ==
  \A s \in Slots : Cardinality(chosen[s]) <= 1

Safety_Persistence ==
  \A s \in Slots : \A v \in Values : [](v \in chosen[s] => [](v \in chosen[s]))

Liveness ==
  \A s \in Slots : <>(Cardinality(chosen[s]) = 1)

=============================================================================