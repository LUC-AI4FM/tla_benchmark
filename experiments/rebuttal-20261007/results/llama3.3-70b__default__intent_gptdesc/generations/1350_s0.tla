```
MODULE Counter
EXTENDS Integers

CONSTANTS None

VARIABLES counter

Init == (counter = 1)

Next == IF counter < 5 THEN counter' = counter + 1 ELSE counter' = counter

Spec == Init /\ [][Next]_counter

THEOREM Spec => []((counter >= 1) /\ (counter <= 5))
THEOREM Spec => <>[](counter = 5)
THEOREM Spec => [](counter' = counter + 1 \/ counter' = counter)

Fairness == WF_vars(Next, counter)

SpecWithFairness == Spec /\ Fairness

THEOREM SpecWithFairness => []((counter >= 1) /\ (counter <= 5))
THEOREM SpecWithFairness => <>[](counter = 5)
THEOREM SpecWithFairness => [](counter' = counter + 1 \/ counter' = counter)

INVARIANT Inv == (counter >= 1) /\ (counter <= 5)

THEOREM SpecWithFairness => Inv
```
Note: The above TLA+ specification models the described system. It includes initialization, allowed state transitions, safety invariants, liveness properties, and fairness conditions as specified.