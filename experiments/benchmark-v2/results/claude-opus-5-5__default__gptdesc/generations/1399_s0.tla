---------------------------- MODULE BooleanFlip ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

\* Simple state predicates about x
TypeOK == x \in BOOLEAN

IsTrue == x = TRUE

IsFalse == x = FALSE

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

\* Safety invariant: x is always a boolean
THEOREM Spec => []TypeOK
=============================================================================