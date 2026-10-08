```
MODULE MutualExclusionLock
EXTENDS Integers

CONSTANTS P1, P2
VARIABLES pc1, pc2, lock

Init == (pc1 = "ncl") ∧ (pc2 = "ncl") ∧ (lock = "free")

Next == 
  ∨ (pc1 = "ncl" ∧ lock = "free" ∧ pc1' = "l1" ∧ pc2' = pc2 ∧ lock' = lock)
  ∨ (pc1 = "l1" ∧ lock = "free" ∧ pc1' = "cs" ∧ pc2' = pc2 ∧ lock' = "locked")
  ∨ (pc1 = "cs" ∧ pc1' = "ncl" ∧ pc2' = pc2 ∧ lock' = "free")
  ∨ (pc2 = "ncl" ∧ lock = "free" ∧ pc1' = pc1 ∧ pc2' = "l2" ∧ lock' = lock)
  ∨ (pc2 = "l2" ∧ lock = "free" ∧ pc1' = pc1 ∧ pc2' = "cs" ∧ lock' = "locked")
  ∨ (pc2 = "cs" ∧ pc1' = pc1 ∧ pc2' = "ncl" ∧ lock' = "free")

Spec == Init ∧ [][Next]_<<pc1, pc2, lock>>
  
MutualExclusion == 
  ¬(pc1 = "cs" ∧ pc2 = "cs")

TypeCorrectness == 
  (pc1 \in {"ncl", "l1", "cs"}) ∧
  (pc2 \in {"ncl", "l2", "cs"}) ∧
  (lock \in {"free", "locked"})

SafetyInvariant == MutualExclusion ∧ TypeCorrectness

LivenessProperty == 
  □(pc1 = "l1" ⇒ ◇(pc1 = "cs"))

THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty
```