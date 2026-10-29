---- MODULE NextStatePredicate ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

\* Predicate that every next-state value must satisfy
ValidValue(v) == v \in 0..9 /\ v % 2 = 0

Init == x = 0

Next == ValidValue(x')

Spec == Init /\ [][Next]_vars

\* Type invariant implied by the constraint
TypeOK == x \in {0, 2, 4, 6, 8}

====