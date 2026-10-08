------------------------------- MODULE StateMachine -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    DOMAIN,  \* The finite set of natural numbers that the state variable can take
    INITIAL_VALUE \* The initial value of the state variable

VARIABLES x

Init == x = INITIAL_VALUE

Next ==
    \/ (x' \in DOMAIN /\ x' = 0) \* Example unconditional assignment
    \/ (x' \in DOMAIN /\ x' = x + 1) \* Example increment
    \/ (x' \in DOMAIN /\ x' = x - 1) \* Example decrement
    \/ (x' \in DOMAIN /\ x' = 5) \* Example conditional assignment if current value is specific
    \/ (x' \in DOMAIN /\ x' \in {x .. x + 2}) \* Example subrange

Spec == Init /\ [][Next]_<<x>>

TypeSafety == x \in DOMAIN

Invariant ==
    TypeSafety /\ x = INITIAL_VALUE

THEOREM Spec => [] Invariant
=============================================================================