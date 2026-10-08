```
MODULE CounterSystem
EXTENDS Integers

CONSTANTS None

VARIABLES counter, pc

Init == (counter = 0) ∧ (pc = "start")

Next == \/ (pc = "start") ∧ (counter < 3) ∧ (counter' = counter + 1) ∧ (pc' = "start")
        ∨ (pc = "start") ∧ (counter = 3) ∧ (counter' = counter) ∧ (pc' = "start")
        ∨ (pc = "start") ∧ (counter' = counter) ∧ (pc' = "start")

Spec == Init ∧ □[Next]_<<counter, pc>>
WeakFairness == WF-vars(Next, <<counter, pc>>)

THEOREM Spec ⇒ □⟨∃ ∞ t : counter[t] = 3 ⟩
INVARIANT Inv == counter ∈ 0..3

SafetyInv == □[(∀ s, t ∈ Nat : (s < t) ⇒ (counter[s] ≤ counter[t]))]
LivenessProp == ⟨∃ ∞ t : counter[t] = 3 ⟩

PROOF Obligation: Spec ∧ WeakFairness ⇒ LivenessProp
```
Note that the `THEOREM` statement is used to specify a proof obligation, which in this case is to prove that under the given specification and fairness condition, the liveness property (i.e., eventually reaching the observable value 3) holds.