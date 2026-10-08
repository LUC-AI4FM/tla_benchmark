------------------------------- MODULE SubsetRelation ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next == /\ b' = (SUBSET S) \subseteq (SUBSET T)
         /\ b' = b' /\ (SUBSET {1, 2}) \subseteq (SUBSET {1, 2, 3})
         /\ b' = b' /\ ~(SUBSET {1, 4}) \subseteq (SUBSET {1, 2, 3})
         /\ b' = b' /\ (SUBSET Int) = (SUBSET Int)
         /\ b' = b' /\ (SUBSET Nat) \subseteq (SUBSET Int)

Spec == Init /\ [][Next]_<<b>>

INVARIANT Inv == /\ b \in BOOLEAN
                 /\ b = TRUE
=============================================================================