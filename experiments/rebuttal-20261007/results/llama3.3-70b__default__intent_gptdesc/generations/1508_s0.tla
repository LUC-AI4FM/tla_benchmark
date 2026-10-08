```
MODULE StateMachine
EXTENDS Integers

CONSTANTS Domain, InitialValue
VARIABLES state

Init == (state = InitialValue)

TypeInvariant == state \in Domain

Next == 
  \/ (state' = 5)              \* unconditional assignment to a fixed value
  \/ (state' \in 1..3)          \* permit next value in a contiguous subrange
  \/ (state = 2 /\ state' = 4) \* guarded by specific current-state value
  \/ (state = 7 /\ state' \in 8..10) \* guarded and within a range

Spec == Init /\ [][Next]_state

THEOREM Spec => []TypeInvariant
THEOREM Spec => [](state = InitialValue)
```