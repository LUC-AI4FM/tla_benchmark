---------------------------- MODULE NextStatePredicate ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == (x = 0)

Next == (x' = x) ∨ (x' ∈ {i ∊ 0..9 : i mod 2 = 0})

Spec == Init ∧ [][Next]_x

THEOREM Spec ⇒ □(x ∈ {i ∊ 0..9 : i mod 2 = 0})
=============================================================================