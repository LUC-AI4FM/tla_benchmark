------------------------------- MODULE MultiInstanceConsensus -------------------------------

CONSTANTS Values, Slots

VARIABLES proposed, chosen

ASSUME Values \subseteq BOOLEAN /\ Cardinality(Values) > 0
ASSUME Slots \subseteq BOOLEAN /\ Cardinality(Slots) > 0

Init == 
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose ==
    \/ /\ EXISTS v \in Values \proposed : proposed' = proposed \cup {v}
       /\ chosen' = chosen
    \/ /\ UNCHANGED proposed
       /\ UNCHANGED chosen

Choose ==
    \/ /\ EXISTS s \in Slots, v \in proposed : 
            chosen[s] = {} 
            /\ chosen'[s] = {v} 
            /\ chosen'[EXCEPT ![s]] = chosen[EXCEPT ![s]]
       /\ proposed' = proposed
    \/ /\ UNCHANGED proposed
       /\ UNCHANGED chosen

Next == Propose \/ Choose

Spec ==
    Init /\ [][Next]_<<proposed, chosen>>

TypeOK ==
    \A s \in Slots : Finite(chosen[s]) /\ chosen[s] \subseteq Values

Nontriviality ==
    \A s \in Slots, v \in chosen[s] : v \in proposed

Stability ==
    \A s \in Slots, v \in chosen[s], <<proposed, chosen>>, <<proposed', chosen'>> \in Next :
        v \in chosen'[s]

Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

Liveness ==
    \A s \in Slots : <>(\E v \in Values : chosen[s] = {v})

LiveSpec ==
    Spec /\ WF_[Next]_<<proposed, chosen>>

=============================================================================