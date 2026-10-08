------------------------------- MODULE ToggleSystem -------------------------------
EXTENDS TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES 
    toggleVar

Init == toggleVar = TRUE

Next == toggleVar' = ~toggleVar

Spec == Init /\ [][Next]_<<toggleVar>>

\* Intentionally violated invariant
InvAlwaysTrue == [](toggleVar = TRUE)

\* State predicate asserting the variable equals true
StatePredTrue == (toggleVar = TRUE)

\* Trivially always satisfied property
TrivialProperty == TRUE

\* Expose the variable directly as a property
ExposeToggleVar == toggleVar

=============================================================================