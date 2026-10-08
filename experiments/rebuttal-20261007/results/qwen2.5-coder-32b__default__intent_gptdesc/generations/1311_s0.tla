------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    A \* Fixed positive integer input
    DOMAIN \* Finite domain for the second input

VARIABLES x, y

Init == /\ x = A
        /\ y \in DOMAIN

Next ==
    \/ /\ y > 0
       /\ \/ /\ x >= y
              /\ x' = x - y
              /\ y' = y
          \/ /\ y > x
             /\ x' = x
             /\ y' = y - x
    \/ /\ y = 0
       /\ x' = x
       /\ y' = y

Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>
    /\ <><Termination>_<<x, y>>

Termination == y = 0

\* Invariants
GCDInvariant ==
    LET GCD(a, b) ==
        IF b = 0 THEN a
        ELSE GCD(b, a % b)
    IN GCD(x, y) = GCD(A, CHOOSE z \in DOMAIN : TRUE)

NonNegative ==
    /\ x >= 0
    /\ y >= 0

BoundedRange ==
    LET maxInit == A + (CHOOSE z \in DOMAIN : TRUE)
    IN /\ x <= maxInit
       /\ y <= maxInit

\* Liveness
TerminationProperty ==
    <><Termination>_<<x, y>>

=============================================================================