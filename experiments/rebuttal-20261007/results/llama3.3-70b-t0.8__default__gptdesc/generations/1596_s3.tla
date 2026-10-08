```
MODULE FastMutex
EXTENDS Integers, FiniteSets

CONSTANTS M, N

VARIABLES x, y, b, pc

Init == 
  (x = 0) ∧ 
  (y = 0) ∧ 
  (b = FALSE) ∧ 
  (pc ∈ ([1..N] → {"Noncritical"}))

Next == 
  ∨ ∃ i ∈ 1..M : 
    (pc[i] = "Noncritical") ∧ 
    (x = 0) ∧ 
    (y ≠ i) ∧ 
    (pc' = [pc EXCEPT ![i] = "Try"]) 
    ∨ (pc[i] = "Try") ∧ 
      ((x' = i) ∧ (pc' = [pc EXCEPT ![i] = "Wait"])) 
    ∨ (pc[i] = "Wait") ∧ 
      ((y ≠ i) ∧ (b' = TRUE) ∧ (pc' = [pc EXCEPT ![i] = "Critical"])) 
    ∨ (pc[i] = "Critical") ∧ 
      ((x' = 0) ∧ (y' = 0) ∧ (b' = FALSE) ∧ (pc' = [pc EXCEPT ![i] = "Noncritical"]))
  ∨ ∃ i ∈ (M+1)..N : 
    (pc[i] = "Noncritical") ∧ 
    (x = 0) ∧ 
    (y ≠ i) ∧ 
    (pc' = [pc EXCEPT ![i] = "Try"]) 
    ∨ (pc[i] = "Try") ∧ 
      ((x' = i) ∧ (pc' = [pc EXCEPT ![i] = "Wait"])) 
    ∨ (pc[i] = "Wait") ∧ 
      ((y ≠ i) ∧ (b' = TRUE) ∧ (pc' = [pc EXCEPT ![i] = "Critical"])) 
    ∨ (pc[i] = "Critical") ∧ 
      ((x' = 0) ∧ (y' = 0) ∧ (b' = FALSE) ∧ (pc' = [pc EXCEPT ![i] = "Noncritical"]))
  ∧ (UNCHANGED <<x, y, b>> ∨ (UNCHANGED <<y, b>> ∧ x' ∈ 1..N))

Spec == Init ∧ [][Next]_<<x, y, b, pc>>
WeakFairness == 
  (∀ i ∈ 1..M : WF Вар(i, Next)) ∧ 
  (∀ i ∈ (M+1)..N : WF Вар(i, Next))
MutualExclusionInvariant == 
  ¬∃ i, j ∈ 1..N : 
    (i ≠ j) ∧ (pc[i] = "Critical") ∧ (pc[j] = "Critical")
LivenessProperty == 
  ∃∀ i ∈ 1..N : ◇□(pc[i] = "Critical")

THEOREM Spec ⇒ []MutualExclusionInvariant
THEOREM Spec ∧ WeakFairness ⇒ LivenessProperty
```