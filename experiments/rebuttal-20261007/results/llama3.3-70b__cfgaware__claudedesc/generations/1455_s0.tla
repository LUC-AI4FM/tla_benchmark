```
MODULE SubsetEqualityTest
VARIABLE b

Init == b = TRUE

Next == b' = 
  (SUBSET (1..23) \subseteq SUBSET (1..42)) /\ 
  ~(SUBSET (1..42) \subseteq SUBSET (1..23)) /\ 
  (SUBSET (2..42) \subseteq SUBSET (1..42)) /\ 
  ~(SUBSET (1..42) \subseteq SUBSET (2..42)) /\ 
  (SUBSET {1,2,3} \subseteq SUBSET {1,2,3,4}) /\ 
  (SUBSET {} \subseteq SUBSET {}) /\ 
  (SUBSET {} \subseteq SUBSET {1}) /\ 
  (SUBSET {1} \subseteq SUBSET Int) /\ 
  (SUBSET {1} \subseteq SUBSET Nat)

Inv == b = TRUE

Spec == Init /\ [][Next]_b
THEOREM Spec => []Inv
```
Note: The `THEOREM` statement is used to specify the property that should be checked by the model checker. In this case, we want to check that the invariant `Inv` holds for all states of the specification `Spec`.