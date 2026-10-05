---------------------------- MODULE BinaryChoice ----------------------------

EXTENDS Naturals

VARIABLES x

\* The set of allowed binary values for nondeterministic choice
BinaryValues == {0, 1}

\* Initial state: existentially choose from binary values with constraint x < 1
Init == \E v \in BinaryValues : v < 1 /\ x = v

\* No transitions modify the variable after initialization (inert/stuttering only)
Next == UNCHANGED x

\* Safety invariant: variable is always strictly less than 1
SafetyInvariant == x < 1

\* Type invariant for completeness
TypeInvariant == x \in BinaryValues

\* Combined invariant
Invariant == TypeInvariant /\ SafetyInvariant

\* The system specification with weak fairness (though Next never changes state)
\* This captures that the system remains stable with no progress possible
Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Liveness property: the system is always stable (x never changes from its initial value)
\* This is expressed as: once initialized, x remains constant forever
Stable == [][\E v \in BinaryValues : x = v /\ x' = v]_x

\* Property asserting no state changes occur (system is inert)
NoProgress == [][x' = x]_x

\* The variable remains at its initial value forever
AlwaysInert == [](ENABLED(Next) => (Next => UNCHANGED x))

=============================================================================