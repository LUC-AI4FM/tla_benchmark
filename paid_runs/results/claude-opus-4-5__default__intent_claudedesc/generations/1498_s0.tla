---------------------------- MODULE BooleanToggle ----------------------------
EXTENDS Booleans

VARIABLES toggle

TypeInvariant == toggle \in BOOLEAN

Init == toggle = FALSE

Toggle1 == toggle' = ~toggle

Toggle2 == toggle' = ~toggle

Next == Toggle1 \/ Toggle2

Spec == Init /\ [][Next]_toggle

=============================================================================