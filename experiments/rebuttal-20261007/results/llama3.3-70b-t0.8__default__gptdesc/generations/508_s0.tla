```
MODULE SmallPlusCalAlgorithm
EXTENDS Integers

CONSTANTS 
VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "Start")
Next == pc = "Start" ∧ (x ^ 2 <= 100) ∧ (pc' = "Done") ∧ (x' = x)
          ∨ (pc /= "Start") ∧ (pc' = pc) ∧ (x' = x)

Spec == Init ∧ □[Next]_<<x, pc>>
Termination == ◇(pc = "Done")

THEOREM Spec => Termination
```