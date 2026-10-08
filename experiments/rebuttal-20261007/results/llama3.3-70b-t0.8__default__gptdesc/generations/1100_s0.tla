```
MODULE MutualExclusionLock
EXTENDS Integers

CONSTANTS P1, P2
VARIABLES pc1, pc2, lock

Init == (pc1 = "ncl") ∧ (pc2 = "ncl") ∧ (lock = "free")

Next == 
  ∨ (pc1 = "ncl" ∧ pc2 ≠ "cs" ∧ lock = "free" ∧ pc1' = "l1" ∧ pc2' = pc2 ∧ lock' = lock)
  ∨ (pc1 = "l1" ∧ lock = "free" ∧ pc1' = "cs" ∧ pc2' = pc2 ∧ lock' = "P1")
  ∨ (pc1 = "cs" ∧ pc1' = "ncl" ∧ pc2' = pc2 ∧ lock' = "free")
  ∨ (pc2 = "ncl" ∧ pc1 ≠ "cs" ∧ lock = "free" ∧ pc1' = pc1 ∧ pc2' = "l2" ∧ lock' = lock)
  ∨ (pc2 = "l2" ∧ lock = "free" ∧ pc1' = pc1 ∧ pc2' = "cs" ∧ lock' = "P2")
  ∨ (pc2 = "cs" ∧ pc1' = pc1 ∧ pc2' = "ncl" ∧ lock' = "free")

Spec == Init ∧ [][Next]_<<pc1, pc2, lock>>

MutualExclusion == 
  ¬(pc1 = "cs" ∧ pc2 = "cs")

SafetyInvariant == MutualExclusion

LivenessProperty == 
  □(pc1 = "l1" ⇒ ◇(pc1 = "cs"))

THEOREM Spec ⇒ []SafetyInvariant
THEOREM Spec ⇒ LivenessProperty
```