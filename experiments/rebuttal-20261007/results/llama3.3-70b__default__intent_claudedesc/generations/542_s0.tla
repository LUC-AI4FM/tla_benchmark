```
MODULE IncrementConcurrently
EXTENDS Integers

CONSTANTS P1Done, P2Done

VARIABLES x, doneP1, doneP2

Init == (x = 0) ∧ (doneP1 = FALSE) ∧ (doneP2 = FALSE)

Next == (¬doneP1 ∧ x' = x + 1 ∧ doneP1' = TRUE ∧ doneP2' = doneP2) ∨
        (¬doneP2 ∧ x' = x + 1 ∧ doneP2' = TRUE ∧ doneP1' = doneP1) ∨
        (doneP1 ∧ doneP2 ∧ x' = x ∧ doneP1' = doneP1 ∧ doneP2' = doneP2)

Spec == Init ∧ [][Next]_<<x, doneP1, doneP2>>
Termination == <>[](doneP1 ∧ doneP2)
THEOREM Spec => []<>Termination
```
Note: The above TLA+ module uses the `[]` operator to specify that `Next` should hold for all steps and the `_` operator to specify stuttering steps where none of the variables change. The `THEOREM` statement asserts that the specification satisfies the liveness property of termination, which means both processes will eventually complete their increments.