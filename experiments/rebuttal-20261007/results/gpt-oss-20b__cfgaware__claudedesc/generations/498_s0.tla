------------------------------ MODULE MultiConsensus ------------------------------
EXTENDS Naturals, FiniteSets, Temporal

CONSTANTS Values, Slots

VARIABLES proposed, chosen

(* --- Definitions --- *)

Init == 
  /\ proposed = {}
  /\ chosen \in [Slots -> SUBSET Values]
  /\ \A s \in Slots : chosen[s] = {}

Propose ==
  LET v == CHOOSE v \in Values \setminus proposed : TRUE
  IN
    /\ proposed' = proposed \cup {v}
    /\ chosen' = chosen

Choose ==
  LET s == CHOOSE s \in Slots : chosen[s] = {} ,
      v == CHOOSE v \in proposed : TRUE
  IN
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ proposed' = proposed

Next == Propose \/ Choose

Spec == Init /\ []Next

LiveSpec == Spec /\ WF_vars[Propose \/ Choose]

(* --- Safety properties --- *)

TypeOK ==
  /\ chosen \in [Slots -> SUBSET Values]
  /\ proposed \subseteq Values
  /\ \A s \in Slots : Finite(chosen[s])

Nontriviality ==
  \A s \in Slots : \A v \in chosen[s] : v \in proposed

Stability ==
  \A s \in Slots :
    [] ((\E v \in Values : chosen[s] = {v}) => [] (chosen[s] = {v}))

Consistency ==
  \A s \in Slots : #chosen[s] <= 1

(* --- Liveness property --- *)

Liveness ==
  \A s \in Slots : <> (chosen[s] != {})

ASSERT TypeOK
ASSERT Nontriviality
ASSERT Stability
ASSERT Consistency

LTLSPEC Liveness

=============================================================================