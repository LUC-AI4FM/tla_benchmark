```
MODULE Counter
EXTENDS Integers

CONSTANTS Threshold
VARIABLES counter

Init == (counter = 0)

Next == 
  IF counter < Threshold THEN 
    OR counter' = counter + 1
    OR counter' = counter
  ELSE 
    counter' = counter

Spec == Init /\ [][Next]_counter

SaturationInvariant == counter <= Threshold
NonDecreasingInvariant == counter' >= counter
NoJumpInvariant == (counter' = counter) \/ (counter' = counter + 1)
TypeInvariant == counter \in Nat

THEOREM Spec => []SaturationInvariant
THEOREM Spec => []NonDecreasingInvariant
THEOREM Spec => []NoJumpInvariant
THEOREM Spec => []TypeInvariant

Liveness == <> (counter = Threshold)

Fairness == WF_vars(Next, counter)
THEOREM Spec /\ Fairness => Liveness
```