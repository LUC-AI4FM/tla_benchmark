---- MODULE SubsetRelation ----
EXTENDS TLC, FiniteSets, Integers

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next ==
    /\ b' \in BOOLEAN
    /\ b' = 
        (SUBSET {x \in 1..5 : x > 0} \subseteq SUBSET {y \in 1..5 : y < 6})
        /\ ~(SUBSET {x \in 1..5 : x > 3} \subseteq SUBSET {y \in 1..2 : y < 6})
        /\ (SUBSET {} \subseteq SUBSET {1, 2, 3})
        /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {})
        /\ (SUBSET Int \subseteq SUBSET Nat)
        /\ ~(SUBSET Nat \subseteq SUBSET (-Nat))

Spec == Init /\ [][Next]_<<b>>

Invariant ==
    /\ b = TRUE
    /\ b \in BOOLEAN
====