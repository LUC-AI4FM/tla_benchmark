```
MODULE MutualExclusionLock
EXTENDS Integers

CONSTANTS P1, P2, locked

VARIABLES pc1, pc2, lock

Init == 
  (pc1 = "ncl") ∧ (pc2 = "ncl") ∧ (lock = FALSE)

Next == 
  ((pc1 = "ncl") ∧ (lock = FALSE) ∧ (pc1' = "l1") ∧ (pc2' = pc2) ∧ (lock' = lock))
  ∨ ((pc1 = "l1") ∧ (lock = FALSE) ∧ (pc1' = "cs") ∧ (pc2' = pc2) ∧ (lock' = TRUE))
  ∨ ((pc1 = "cs") ∧ (pc1' = "ncl") ∧ (pc2' = pc2) ∧ (lock' = FALSE))
  ∨ ((pc2 = "ncl") ∧ (lock = FALSE) ∧ (pc1' = pc1) ∧ (pc2' = "l1") ∧ (lock' = lock))
  ∨ ((pc2 = "l1") ∧ (lock = FALSE) ∧ (pc1' = pc1) ∧ (pc2' = "cs") ∧ (lock' = TRUE))
  ∨ ((pc2 = "cs") ∧ (pc1' = pc1) ∧ (pc2' = "ncl") ∧ (lock' = FALSE))

Spec == Init ∧ [][Next]_<<pc1, pc2, lock>>

SafetyInv == 
  (pc1 = "cs") ⇒ (pc2 ≠ "cs")
  ∧ (pc2 = "cs") ⇒ (pc1 ≠ "cs")

LivenessProp == 
  [](pc1 = "l1") → <> (pc1 = "cs")

THEOREM Spec ⇒ []SafetyInv
THEOREM Spec ⇒ LivenessProp

Fairness == SF_VARIABLES(pc1, pc2)
```
Note: In TLA+, the `SF_VARIABLES` operator asserts strong fairness for a set of variables. It ensures that if a variable is continuously enabled to make a step, then it will eventually do so.