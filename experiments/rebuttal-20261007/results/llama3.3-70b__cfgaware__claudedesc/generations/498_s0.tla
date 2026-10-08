---------------------------- MODULE MultiInstanceConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Values, Slots
VARIABLE proposed, chosen

TypeOK == /\ proposed \subseteq Values
          /\ chosen \in [Slots -> SUBSET Values]

Nontriviality == proposed = UNION {chosen[slot] : slot \in Slots}

Stability == chosen' = chosen

Consistency == \A slot \in Slots : Cardinality(chosen[slot]) \leq 1

Propose == /\ ~ (proposed = Values)
           /\ \E v \in (Values \ proposed) : proposed' = proposed \cup {v}
           /\ UNCHANGED chosen

Choose == /\ \E slot \in Slots : chosen[slot] = {}
           /\ \E v \in proposed : chosen' = [chosen EXCEPT ![slot] = {v}]
           /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == /\ TypeOK
         /\ proposed = {} /\ chosen = [s \in Slots |-> {}]
         /\ [][Next]_<<proposed, chosen>>
         /\ WF_vars(<<Propose, Choose>>)_<<proposed, chosen>>

LiveSpec == Spec /\ SF_vars(<<Propose, Choose>>)_<<proposed, chosen>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => []Stability
THEOREM Spec => []Consistency

Liveness == <> \A slot \in Slots : chosen[slot] # {}

THEOREM LiveSpec => Liveness
======================================================================================