```
MODULE SubsetRelation
EXTENDS Integers, FiniteSets, Nat
CONSTANTS S, T
VARIABLES b

Init ==
  b = TRUE

Next ==
  b' = (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}) /\ 
       ~(SUBSET {1, 2} \subseteq SUBSET {3, 4}) /\
       (SUBSET Int \subseteq SUBSET Int) /\ 
       ~(SUBSET Nat \subseteq SUBSET Int) /\ 
       (SUBSET {} \subseteq SUBSET {a \in Nat : a > 0}) /\ 
       (SUBSET {n \in Nat : n < 5} \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

Inv == b \in BOOLEAN /\ b = TRUE
```