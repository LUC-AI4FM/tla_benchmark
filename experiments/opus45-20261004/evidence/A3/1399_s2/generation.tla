---------------------------- MODULE BooleanToggle ----------------------------

EXTENDS Booleans

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

IsTrue == x = TRUE

IsFalse == x = FALSE

TypeInvariant == x \in BOOLEAN

=============================================================================