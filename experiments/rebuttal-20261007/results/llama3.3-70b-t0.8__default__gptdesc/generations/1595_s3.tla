```
MODULE SimpleFairCounter
EXTENDS Integers
CONSTANTS
VARIABLES pc, x

Init == (pc = "Start") ∧ (x = 0)

Next == 
  IF pc = "Start" THEN 
    ((pc' = "Loop") ∧ (x' = 0)) ∨ 
    ((pc' = "Done") ∧ (x' = x))
  ELSE IF pc = "Loop" THEN 
    ((x < 10) ∧ (pc' = "Loop") ∧ (x' = x + 1)) ∨
    ((x = 10) ∧ (pc' = "Done") ∧ (x' = x))
  ELSE (pc' = pc) ∧ (x' = x)

Spec == Init ∧ [][Next]_<<pc, x>>
Termination == <>[pc = "Done"]_pc

AtFive == (x = 5)
FinishLoop == (x = 10)
PossibleCounts == (pc = "Start") ∨ (pc = "Loop") ∨ (pc = "Done")

THEOREM Spec => []Termination
```
Note: This module is written in the standard TLA+ syntax and should be compatible with TLC, the model checker provided by the TLA+ Toolbox.