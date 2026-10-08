```
MODULE StateTransitionSystem
EXTENDS Integers

CONSTANTS Op, InvariantSet
VARIABLES state

Init == state = 0

Next == 
  /\ state' \in Op(state)
  /\ state' \in InvariantSet

Spec == Init /\ [][Next]_state

Invariant == state \in InvariantSet

Liveness == <>[]<>(~ (Op(state) = {}))

Fairness == WF_state(Next)

Reachability(P) == <>[]<>(P(state))

DeadlockFreedom == []<>~(Op(state) = {})

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
THEOREM Spec => Fairness
THEOREM Spec => DeadlockFreedom
```
Note: The `THEOREM` statements are used to specify the properties that should be verified by a model checker. They can be removed if not needed.