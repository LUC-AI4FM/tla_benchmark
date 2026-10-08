```tla
MODULE SubsetConstraintExample
EXTENDS Integers, FiniteSets

CONSTANTS Universe

VARIABLES subsetVar, constantVar

Init ==
  /\ subsetVar \subseteq {1, 2}
  /\ constantVar = {1, 2, 3}

Next ==
  /\ constantVar' = constantVar
  /\ subsetVar' \subseteq constantVar

Spec == Init /\ [][Next]_<<subsetVar, constantVar>>

THEOREM Spec => []Invariant1
PROOF * (omit proof)

THEOREM Spec => []Invariant2
PROOF * (omit proof)

Invariant1 == subsetVar \subseteq Universe

Invariant2 == ENABLED (subsetVar' \subseteq {1})

StatePredicate1 == subsetVar = constantVar

StatePredicate2 == {3} \subseteq subsetVar'

POSTCONDITION ==
  /\ _POSSIBLE <<StatePredicate1>> = 1
  /\ _POSSIBLE <<StatePredicate2>> = 0
```