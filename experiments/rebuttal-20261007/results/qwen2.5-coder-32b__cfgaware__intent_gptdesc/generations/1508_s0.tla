------------------------------- MODULE StateMachineSpec -------------------------------

CONSTANTS 
    DOMAIN,          \* The finite set of natural numbers that the state variable can take.
    INITIAL_VALUE    \* The unique initial value for the state variable.

VARIABLES 
    state            \* The integer-valued state variable.

ASSUME
    /\ DOMAIN \subseteq Nat
    /\ INITIAL_VALUE \in DOMAIN

Init == state = INITIAL_VALUE

Next ==
    \/ (state' = 0)                                      \* Unconditional assignment to a fixed value.
    \/ (state' \in {s \in DOMAIN | s > state})           \* Permit the next value to lie in a contiguous subrange.
    \/ (state = 1 /\ state' \in {2, 3})                  \* Guarded by specific current-state values.

Spec == Init /\ [][Next]_<<state>>

TypeSafety == state \in DOMAIN

Invariant ==
    /\ TypeSafety
    /\ state = INITIAL_VALUE                             \* This is a placeholder for the global invariant. Adjust as needed.

THEOREM Spec => []Invariant

=============================================================================