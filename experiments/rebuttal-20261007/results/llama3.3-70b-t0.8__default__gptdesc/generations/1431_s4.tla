```
MODULE TwoStateProcess
EXTENDS Integers, Sequences

CONSTANTS Done
VARIABLES pc, history

Init == (pc = "A") ∧ (history = <<>>)

Next == 
  ∨ (pc = "A") ∧ (pc' = "B") ∧ (history' = Append(history, "A"))
  ∨ (pc = "B") ∧ (pc' = "A") ∧ (history' = history)
  ∨ (pc' = pc) ∧ (history' = history)

Spec == Init ∧ [][Next]_<<pc, history>>
          ∧ WF_<<pc, history>>([A \/ B]_<<pc, history>>)

StateConstraint == Len(history) <= 5

Liveness == <> (pc = "Done")

THEOREM Spec => [] StateConstraint
THEOREM Spec => Liveness
```