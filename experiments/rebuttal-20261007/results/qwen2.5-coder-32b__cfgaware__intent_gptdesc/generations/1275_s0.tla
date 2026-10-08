------------------------------- MODULE SimpleStateVarSystem -------------------------------

CONSTANTS
    \* No additional constants are needed for this specification

VARIABLES
    value

Init == \/ value = 0

Next == TRUE

Spec == Init /\ [][Next]_<<value>>

Invariant == value < 1

Stability == [](value' = value)

TypeOK == value \in {0, 1}

\* The behavior of the system is defined by the initial condition and the fact that no changes occur after initialization
BehaviorSpecification ==
    \/ /\ Init
       /\ [][Next]_<<value>>
       /\ Invariant
       /\ Stability

THEOREM Spec => BehaviorSpecification

=============================================================================