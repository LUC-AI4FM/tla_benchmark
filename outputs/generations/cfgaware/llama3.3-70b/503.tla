---------------------------- MODULE SingleValueConsensus ----------------------------
EXTENDS Integers

CONSTANT Values
VARIABLE chosen

Init == (chosen = {})

Next == (chosen = {}) /\ (chosen' = {v} /\ v \in Values) \/ 
        (chosen /= {}) /\ (chosen' = chosen)

Spec == Init /\ [][Next]_chosen

AtMostOneTheorem == []((chosen = {}) \/ (Cardinality(chosen) = 1))

LiveSpec == Spec /\ WF_vars(Next, <<chosen>>)
=============================================================================