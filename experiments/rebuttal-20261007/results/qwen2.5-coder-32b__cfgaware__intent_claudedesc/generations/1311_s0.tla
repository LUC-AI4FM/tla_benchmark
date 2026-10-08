------------------------------- MODULE EuclidsGCD -------------------------------

CONSTANTS
    \* The initial value of A
    InitA,
    \* The possible values for B
    PossibleBValues

VARIABLES
    \* Variable A in the GCD algorithm
    A,
    \* Variable B in the GCD algorithm
    B,
    \* Indicates if the algorithm is done
    done

ASSUME
    InitA = 24,
    PossibleBValues = {1..50}

CONSTANT
    \* The initial value of B, chosen nondeterministically from PossibleBValues
    InitB \in PossibleBValues

INIT
    /\ A = InitA
    /\ B = InitB
    /\ done = FALSE

NEXT ==
    \/ /\ A # 0
       /\ (A < B => \/ /\ A' = B
                           /\ B' = A - B
                      \/ /\ A' = A - B
                         /\ B' = B)
       /\ done' = FALSE
    \/ /\ A = 0
       /\ B' = B
       /\ done' = TRUE

SPECIFICATION
    \* The algorithm terminates in finite steps and reaches a done state
    Spec == /\ Init
            /\ [][NEXT]_<<A, B, done>>
            /\ <><done = TRUE>_<<A, B, done>>

===============================================================================