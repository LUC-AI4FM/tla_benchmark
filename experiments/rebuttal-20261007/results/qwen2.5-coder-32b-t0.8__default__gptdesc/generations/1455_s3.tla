```tla
MODULE SubsetRelation

EXTENDS Integers, FiniteSets, TLC

CONSTANTS S, T

VARIABLES b

Init == b = TRUE

Next ==
    /\ b' \in BOOLEAN
    /\ b' = 
        (SUBSET {1, 2, 3} \subseteq SUBSET {1, 2, 3, 4})
        /\ ~(SUBSET {1, 2, 3, 4} \subseteq SUBSET {1, 2, 3})
        /\ (SUBSET {} \subseteq SUBSET {})
        /\ (SUBSET {5} \subseteq SUBSET Int)
        /\ ~(SUBSET Int \subseteq SUBSET {5})
        /\ (SUBSET Nat \subseteq SUBSET Int)

Spec == Init /\ [][Next]_<<b>>

INVARIANT b = TRUE
```