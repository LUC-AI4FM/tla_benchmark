------------------------------- MODULE SubsetRelation -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next ==
    /\ b' \in BOOLEAN
    /\ b' = 
        (SUBSET {1, 2, 3} \subseteq SUBSET {1, 2, 3})
        /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {4, 5, 6})
        /\ (SUBSET Int \subseteq SUBSET Nat)
        /\ ~(SUBSET {x \in Int : x > 0} \subseteq SUBSET {x \in Int : x < 0})
        /\ (SUBSET {} \subseteq SUBSET {})
        /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})

Spec ==
    /\ Init
    /\ [][Next]_<<b>>

Invariant == b = TRUE

=============================================================================