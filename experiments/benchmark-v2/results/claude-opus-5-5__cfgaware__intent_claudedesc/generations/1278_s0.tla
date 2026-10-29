---- MODULE NextStatePredicate ----
EXTENDS Integers

VARIABLE x

vars == <<x>>

\* The predicate every next-state value must satisfy
P(v) == v \in 0..9 /\ v % 2 = 0

Init == x = 0

Next == P(x')

Spec == Init /\ [][Next]_vars

TypeOK == x \in 0..9
====