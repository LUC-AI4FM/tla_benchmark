```
MODULE Lock
EXTENDS Integers

CONSTANTS P1, P2
VARIABLES lock, pc1, pc2

Init == (lock = 0) ∧ (pc1 = "ncs") ∧ (pc2 = "ncs")

Next == 
  ∨ (pc1 = "ncs" ∧ lock = 0 ∧ pc1' = "wait" ∧ lock' = 1 ∧ pc2' = pc2)
  ∨ (pc1 = "wait" ∧ lock = 1 ∧ pc1' = "cs" ∧ lock' = 1 ∧ pc2' = pc2)
  ∨ (pc1 = "cs" ∧ pc1' = "post" ∧ lock' = lock ∧ pc2' = pc2)
  ∨ (pc1 = "post" ∧ pc1' = "ncs" ∧ lock' = 0 ∧ pc2' = pc2)
  ∨ (pc2 = "ncs" ∧ lock = 0 ∧ pc2' = "wait" ∧ lock' = 1 ∧ pc1' = pc1)
  ∨ (pc2 = "wait" ∧ lock = 1 ∧ pc2' = "cs" ∧ lock' = 1 ∧ pc1' = pc1)
  ∨ (pc2 = "cs" ∧ pc2' = "post" ∧ lock' = lock ∧ pc1' = pc1)
  ∨ (pc2 = "post" ∧ pc2' = "ncs" ∧ lock' = 0 ∧ pc1' = pc1)

Spec == Init ∧ [][Next]_<<lock, pc1, pc2>>
TypeInvariant == (lock \in {0, 1}) ∧ (pc1 \in {"ncs", "wait", "cs", "post"}) ∧ (pc2 \in {"ncs", "wait", "cs", "post"})
MutualExclusionInvariant == 
  ¬(pc1 = "cs" ∧ pc2 = "cs") ∧
  ¬(pc1 = "post" ∧ pc2 = "cs") ∧
  ¬(pc1 = "cs" ∧ pc2 = "post") ∧
  (lock = 1 ⇒ (pc1 = "wait" ∨ pc1 = "cs" ∨ pc1 = "post" ∨ pc2 = "wait" ∨ pc2 = "cs" ∨ pc2 = "post"))

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusionInvariant

Fairness == WF_<<lock, pc1, pc2>>(Next)
```
Note: This TLA+ specification uses the `WF_` operator to specify weak fairness for the `Next` action. The `THEOREM` statements are used to specify the type-correctness invariant and mutual-exclusion invariant as properties that should be verified by TLAPS proofs.