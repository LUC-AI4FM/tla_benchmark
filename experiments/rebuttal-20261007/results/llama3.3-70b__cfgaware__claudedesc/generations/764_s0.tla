```
MODULE Spec
EXTENDS Integers, FiniteSets

CONSTANT NP

VARIABLE forks, hungry

vars == <<forks, hungry>>

Init ==
  /\ forks = [i \in 1..NP |-> [holder |-> IF i = 2 THEN 1 ELSE (i - 1), clean |-> FALSE]]
  /\ hungry = [p \in 1..NP |-> TRUE]

Loop(p) ==
  /\ forks[p] = [holder |-> p, clean |-> FALSE] \/ forks[(p + 1) % NP + 1] = [holder |-> p, clean |-> FALSE]
  /\ IF hungry[p]
    THEN IF forks[p] = [holder |-> p, clean |-> TRUE] /\ forks[(p + 1) % NP + 1] = [holder |-> p, clean |-> TRUE]
           THEN Eat(p)
           ELSE Skip
      ELSE Think(p)

Eat(p) ==
  /\ hungry' = [hungry EXCEPT ![p] = FALSE]
  /\ forks' = [forks EXCEPT ![p] = [holder |-> p, clean |-> FALSE]]
  /\ forks'[(p + 1) % NP + 1] = [holder |-> p, clean |-> FALSE]

Think(p) ==
  /\ hungry' = [hungry EXCEPT ![p] = TRUE]
  /\ forks' = forks
  /\ UNCHANGED <<forks, hungry>>

Next ==
  \/ \E p \in 1..NP : Loop(p)
  \/ \E p \in 1..NP : Eat(p)
  \/ \E p \in 1..NP : Think(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ forks \in [1..NP -> [holder: Int, clean: Bool]]
  /\ hungry \in [1..NP -> Bool]

ExclusiveAccess ==
  \A p, q \in 1..NP : ~(forks[p] = [holder |-> p, clean |-> TRUE] /\ forks[(p + 1) % NP + 1] = [holder |-> q, clean |-> TRUE])

NobodyStarves == <>[](~\E p \in 1..NP : hungry[p])

THEOREM Spec => []TypeOK
THEOREM Spec => []ExclusiveAccess
THEOREM Spec => NobodyStarves
```
Note: The `UNCHANGED` operator is used to specify that the `forks` and `hungry` variables are not changed in the `Think(p)` step. The `Skip` statement is not explicitly needed, as the `ELSE` branch of the conditional statement will simply not modify any variables if the condition is false.

Also note that this specification uses the `EXCEPT` operator to update the `forks` and `hungry` functions in a concise way. This operator creates a new function that is equal to the original function, except for the specified changes.

The `THEOREM` statements at the end specify the properties that should be verified by the model checker. The first two theorems verify that the `TypeOK` and `ExclusiveAccess` invariants are always true, while the third theorem verifies that the `NobodyStarves` liveness property is satisfied.