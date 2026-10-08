```
MODULE Counter
EXTENDS Integers

CONSTANTS 

VARIABLES pc, x

Init == (pc = "Start") ∧ (x = 0)

Next == IF pc = "Start" THEN
            pc' = "Loop" ∧ x' = 0
          ELSE IF pc = "Loop" THEN
            IF x < 10 THEN
              pc' = "Loop" ∧ x' = x + 1
            ELSE
              pc' = "Done" ∧ x' = x
            END
          ELSE
            FALSE
          END

Spec == Init ∧ □[Next]_pc ∧ WF_pc(Next)

AtFive == (x = 5)
FinishLoop == (pc = "Loop") ∧ (x = 10)
PossibleCounts == ∃ counts ∈ [0..10] : counts = x

THEOREM Spec ⇒ □((pc = "Done") ∨ FinishLoop)
THEOREM Spec ⇒ ♢(pc = "Done")
```
Note: The `WF_pc(Next)` condition asserts weak fairness of the `Next` action with respect to the `pc` variable, ensuring that if `Next` is continuously enabled for some value of `pc`, it will eventually be taken.