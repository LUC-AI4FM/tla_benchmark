---------------------------- MODULE BooleanStateMachine ----------------------------
EXTENDS Booleans

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

\* Simple state predicates about x
IsTrue == x = TRUE
IsFalse == x = FALSE

\* Safety invariant: x is always a boolean value
TypeInvariant == x \in BOOLEAN

===================================================================================