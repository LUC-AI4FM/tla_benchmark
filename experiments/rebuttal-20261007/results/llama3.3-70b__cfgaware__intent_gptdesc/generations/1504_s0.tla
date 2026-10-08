```
MODULE SimpleReactiveSystem
VARIABLES state

Init == state = TRUE

Next == state' = state

Prop == [](state = TRUE) ∧ ◇□(Next)
```

However, to accurately express liveness in TLA+, we should use the `WF_vars` (weak fairness) or `SF_vars` (strong fairness) operator. Since our system allows stuttering steps and never deadlocks due to the nature of `Next`, we can assert that it's always possible to take a step without changing the state, thus ensuring liveness. Here is the corrected version:

```
MODULE SimpleReactiveSystem
VARIABLES state

Init == state = TRUE

Next == state' = state

Prop == [](state = TRUE) ∧ WF_state(Next)
```

This specification defines `Init` as the initial condition where `state` is `TRUE`, `Next` as the next-state relation that does not change `state`, and `Prop` as the property that asserts `state` remains `TRUE` forever (`[]`) and that it's always possible to take a step (liveness, expressed via weak fairness `WF_state(Next)`). This ensures both safety (the state never changes from `TRUE`) and liveness (a next step is always enabled) properties.