```
MODULE SubsetRelation
EXTENDS Integers, FiniteSets, Naturals
CONSTANTS S, T
VARIABLES b

Init == b = TRUE

Next == b' = (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}) /\ 
             ~(SUBSET {1, 2} \subseteq SUBSET {3, 4}) /\ 
             (SUBSET Int \subseteq SUBSET Int) /\ 
             ~(SUBSET Nat \subseteq SUBSET Int) /\ 
             (SUBSET {} \subseteq SUBSET {1, 2}) /\ 
             (SUBSET {1, 2} \subseteq SUBSET {1, 2})

Spec == Init /\ [][Next]_b

Invariant == b \in BOOLEAN /\ b = TRUE
```