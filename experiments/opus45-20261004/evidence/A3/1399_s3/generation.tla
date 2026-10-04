```tla
MODULE BooleanStateMachine

EXTENDS Booleans

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

XIsTrue == x = TRUE

XIsFalse == x = FALSE

TypeInvariant == x \in BOOLEAN

```