```
MODULE ToggleSystem
EXTENDS Integers, Bool

CONSTANTS None

VARIABLES state

Init == state = TRUE

Next == state' = ~state ∨ state' = state

Spec == Init ∧ □[Next]_state

StrongInv == □(state ∈ {TRUE, FALSE})
WeakInv == ◇□(state = TRUE)

Safety == StrongInv ∧ Spec
Liveness == ♡◇(state = ~state) ∧ ♡◇(state = state)

THEOREM Spec => []<>Liveness
THEOREM Spec => Safety

=============================================================================
```
Note: The `None` constant is declared as per TLA+ requirements, but it's not used in the specification. Also, `□[Next]_state` denotes a "stuttering" step where `state` doesn't change, and `~state` represents the logical negation of `state`. The `THEOREM` statements are included to facilitate model checking and proof obligations for the specified properties.