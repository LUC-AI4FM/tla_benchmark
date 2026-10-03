------------------------------- MODULE SubsetRelation ------------------------------

VARIABLES b

CONSTANTS S, T

Init == b = TRUE

SUBSET_RELATION_ASSERTIONS ==
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
    /\ ~(SUBSET {1, 4} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {} \subseteq SUBSET {})
    /\ (SUBSET Int \subseteq SUBSET Nat)
    /\ ~(SUBSET Nat \subseteq SUBSET Int)

Next == b' = SUBSET_RELATION_ASSERTIONS

Spec == Init /\ [][Next]_<<b>>

TypeOK == b \in BOOLEAN

Inv == TypeOK /\ b = TRUE

=============================================================================