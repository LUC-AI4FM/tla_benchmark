```tla+
MODULE BooleanStateMachine
EXTENDS Booleans

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

XIsTrue == x = TRUE

XisFalse == x = FALSE

TypeInvariant == x \in BOOLEAN

=============================================================================
```