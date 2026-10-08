```tla
MODULE SubsetOfPowersetTest
VARIABLE testResult

Init ==
  testResult = 
    (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}) /
    \* Powerset of smaller range is subset of powerset of larger range *\
    (SUBSET {1, 2, 3} \subseteq SUBSET {1, 2}) =
    FALSE /
    \* But not vice versa *\
    (SUBSET {1, 2} \subseteq SUBSET {1}) =
    FALSE /
    \* Removing an element yields a powerset that is a subset of the original but not the reverse *\
    (SUBSET {} \subseteq SUBSET {1, 2}) /
    \* Powerset of empty set is subset of itself and any other powerset *\
    (SUBSET {1, 2} \subseteq SUBSET {}) =
    FALSE /
    \* But not vice versa *\
    (SUBSET {{}, {1}} \subseteq SUBSET {{}, {1}, {2}}) /
    \* Nested set inclusions work for small explicit sets *\
    (SUBSET {} \subseteq SUBSET {{}, {1}, {2}}) /
    \* Powerset of empty set is subset of any other powerset *\
    (SUBSET {1} \subseteq SUBSET 1..10) /
    \* Powerset of singleton is subset of powerset of integers and natural numbers *\
    (SUBSET {1} \subseteq SUBSET Nat)

Next ==
  testResult' = testResult

Inv ==
  testResult \in BOOLEAN
```