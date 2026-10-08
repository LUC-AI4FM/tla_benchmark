```
MODULE SubsetRelation
EXTENDS Integers, FiniteSets, Naturals
CONSTANTS S, T
VARIABLES b

Init == (b = TRUE)

Next == (b' = (({1, 2} \subseteq {1, 2, 3}) /\ 
            ({1, 2} \subseteq {1, 2, 3}) /\ 
            ({4, 5} \notin {1, 2, 3}) /\ 
            (Int \subseteq Int) /\ 
            (Nat \subseteq Nat) /\ 
            ({1, 2, 3} \subseteq Nat)))

Spec == Init /\ [][Next]_b

Inv == b \in BOOLEAN /\ b = TRUE
THEOREM Spec => []Inv
```