```
MODULE EuclidGCD
EXTENDS Integers

CONSTANTS MaxValue
VARIABLES a, b, done

Init == (a = 24) ∧ (b ∈ 1..50) ∧ (done = FALSE)

Next == IF done
           THEN UNCHANGED <<a, b, done>>
           ELSE IF a ≠ 0
                  THEN IF a < b
                           THEN (a′ = b) ∧ (b′ = a) ∧ (done′ = done)
                           ELSE (a′ = a - b) ∧ (b′ = b) ∧ (done′ = done)
                  ELSE (done′ = TRUE) ∧ UNCHANGED <<a, b>>

Spec == Init ∧ [][Next]_<<a, b, done>>
Termination == <>(done = TRUE)

THEOREM Spec ⇒ Termination
```