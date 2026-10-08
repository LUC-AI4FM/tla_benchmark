```
MODULE MinimalTwoStateSystem
VARIABLES pc, history

Init == (pc = "A") ∧ (history = <<>>)

A == (pc = "A") ∧ (pc' = "B") ∧ (history' = Append(history, "A"))
B == (pc = "B") ∧ (pc' = "A") ∧ (history' = history)

Next == A ∨ B
Spec == Init ∧ □[Next]_<<pc, history>> ∧ WF_(A ∨ B)(<<pc, history>>)
Constraint == Len(history) < 3
Prop == ◇(pc = "Done")
THEOREM Spec ⇒ Prop
```
Note: This TLA+ module is designed to illustrate a warning that arises when a liveness property is checked in combination with a state constraint. The `Prop` property will be violated because the system never reaches the state `"Done"`. However, due to the `Constraint`, the model checker may not explore all possible traces, potentially producing misleading verification results.