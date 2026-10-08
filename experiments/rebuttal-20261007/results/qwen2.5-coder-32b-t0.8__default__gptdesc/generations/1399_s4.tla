------------------------------ MODULE BooleanStateMachine ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* No constants defined in this specification

VARIABLES 
    x

Init == x = TRUE

Next == x' = ~x

Spec ==
    /\ Init
    /\ [][Next \/ UNCHANGED x]_<<x>>
    
StatePredicates ==
    /\ StableX <=> [](UNCHANGED x)
    /\ FlippingX <=> <>[x \/ x']_<<x>>

=============================================================================