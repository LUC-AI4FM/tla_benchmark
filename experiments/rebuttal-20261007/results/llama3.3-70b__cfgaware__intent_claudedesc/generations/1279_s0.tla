---------------------------- MODULE NextStateRelation ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == x = 23

Next == (x' = 0 ∨ x' = 1) ∧ x' > 0

Stutter == x' = x

NextValue == Next ∨ Stutter

Spec == Init ∧ [][NextValue]_x

THEOREM Spec => []x ≠ 0
=============================================================================