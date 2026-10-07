```
MODULE SubsetEqualityTest
EXTENDS Integers, FiniteSets
CONSTANTS
VARIABLES b

Init == b = TRUE

Next == b' = 
  (SUBSET (1..23) \subseteq SUBSET (1..42)) /
  \ (SUBSET (1..42) \subseteq SUBSET (1..23)) /
  (SUBSET (2..42) \subseteq SUBSET (1..42)) /
  \ (SUBSET (1..42) \subseteq SUBSET (2..42)) /
  (SUBSET {1,2,3} \subseteq SUBSET {1,2,3,4}) /
  (SUBSET {} \subseteq SUBSET {}) /
  (SUBSET {} \subseteq SUBSET {1}) /
  (SUBSET {1} \subseteq SUBSET Int) /
  (SUBSET {1} \subseteq SUBSET Nat) /
  \ (SUBSET Int \subseteq SUBSET {1})

Inv == b = TRUE

Spec == Init /\ [][Next]_b
```