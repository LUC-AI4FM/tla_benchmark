```
MODULE EuclideanAlgorithm
VARIABLES x, y, initialB
CONSTANTS A, N

Init == (x = A) ∧ (y ∈ 1..N) ∧ (initialB = y)

Next == ∨ (x < y ∧ x' = y ∧ y' = x)
          ∨ (x ≥ y ∧ (x' = x - y ∧ y' = y) ∨ (x' = x ∧ y' = y - x))

Spec == Init ∧ [][Next]_<<x, y>>

Termination == (x = 0) ∨ (y = 0)

Inv == ∃ d ∈ Nat ∖ {0} ∷ 
        (d divides x) ∧ (d divides y) ∧ 
        (d divides A) ∧ (d divides initialB) ∧ 
        (∀ e ∈ Nat ∖ {0} ∷ 
           ((e divides x) ∧ (e divides y) ∧ (e divides A) ∧ (e divides initialB)) ⇒ (e divides d))

THEOREM Spec ⇒ []Inv
THEOREM Spec ⇒ WF_<<x, y>>(Next)
THEOREM Spec ∧ Termination ⇒ (x = 0 ∧ y = GCD(A, initialB)) ∨ (y = 0 ∧ x = GCD(A, initialB))
```
Note: The `GCD` operator is assumed to be defined elsewhere in the TLA+ specification or in a separate module. If not, it can be defined as follows:
```
GCD(a, b) == IF a = 0 THEN b ELSE GCD(b % a, a)
```