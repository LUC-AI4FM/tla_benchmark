---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers

CONSTANT InitialValue, MaxValue
VARIABLES a, b, done

Init == (a = 24) ∧ (b ∈ 1..50) ∧ (done = FALSE)

Next == IF a ≠ 0
        THEN IF a < b
             THEN (a′ = b) ∧ (b′ = a) ∧ (done′ = done)
             ELSE (a′ = a - b) ∧ (b′ = b) ∧ (done′ = done)
        ELSE (a′ = a) ∧ (b′ = b) ∧ (done′ = TRUE)

Spec == Init ∧ [][Next]_<<a, b, done>>
THEOREM Spec ⇒ ◇[]done
=============================================================================