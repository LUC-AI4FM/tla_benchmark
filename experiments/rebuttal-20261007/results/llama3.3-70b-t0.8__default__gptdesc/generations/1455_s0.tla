```
MODULE SubsetSystem
EXTENDS Integers, FiniteSets
CONSTANTS S, T
VARIABLES b

Init == b = TRUE

Next == b' = (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}) /\ 
            ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2}) /\ 
            (SUBSET {} \subseteq SUBSET Int) /\ 
            (SUBSET Nat \subseteq SUBSET Int) /\ 
            ~(SUBSET Int \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

Inv == b \in BOOLEAN /\ b = TRUE
```