```
MODULE SimpleStateTransitionSystem
VARIABLE state

Constant Op, Forty2

Init == (state = 0)

Next == state' \in Op(state)

Spec == Init /\ [][Next]_state

THEOREM Spec => []<>~(state \in Op(state)) => <>~(state \in Forty2)
THEOREM Spec => []<>(Op(state) = {}) => <>[](state \in Forty2)

Inv == state \in Forty2

THEOREM Spec => []Inv
THEOREM Spec => <><>Inv

DeadlockFree == [](Op(state) # {})
THEOREM Spec => DeadlockFree => <>~(state \in Op(state))
```
Note: In TLA+, `#` denotes the "not equal to" operator, and `\in` is used for set membership. The `[]` and `<>` operators are used for "always" and "eventually", respectively. The `_` symbol in `[Next]_state` indicates that `Next` is a action (a relation between states) and `state` is the variable being updated.