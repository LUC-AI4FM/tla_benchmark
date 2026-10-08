---------------------------- MODULE Consensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Values
VARIABLE chosen

Init == (chosen = {})

Next == IF chosen = {} THEN
           EXISTS v \in Values : chosen' = {v}
         ELSE
           chosen' = chosen

Spec == Init /\ [][Next]_chosen

TypeOK == chosen \subseteq Values

ConsistencyInv == Cardinality(chosen) <= 1

LiveSpec == Spec /\ WF_vars(Next)

Success == <> ~ (chosen = {})

THEOREM Spec => []TypeOK
THEOREM Spec => []ConsistencyInv
THEOREM LiveSpec => Success

=============================================================================