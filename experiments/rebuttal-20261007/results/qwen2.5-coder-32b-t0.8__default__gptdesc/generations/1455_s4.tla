------------------------------ MODULE SubsetSpec ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next ==
    /\ b' \in BOOLEAN
    /\ b' = (SUBSET {1..5} \subseteq SUBSET {1..10})
       /\ (\neg (SUBSET {1..5} \subseteq SUBSET {1..3}))
       /\ (SUBSET {} \subseteq SUBSET {})
       /\ (SUBSET {1, 2, 3} \subseteq SUBSET Int)
       /\ (\neg (SUBSET Nat \subseteq SUBSET {1, 2, 3}))

Spec ==
    /\ Init
    /\ [][Next]_<<b>>

Invariant ==
    /\ b \in BOOLEAN
    /\ b = TRUE

=============================================================================