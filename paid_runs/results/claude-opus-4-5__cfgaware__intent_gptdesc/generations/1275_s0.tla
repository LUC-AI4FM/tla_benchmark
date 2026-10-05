---------------------------- MODULE specification ----------------------------

VARIABLE x

\* The set of allowed binary values
BinaryValues == {0, 1}

\* Initial state: nondeterministically choose a binary value (0 or 1)
\* subject to the constraint that the initial value must be strictly less than 1
Init == \E v \in BinaryValues : (v < 1) /\ (x = v)

\* After initialization, the state must remain unchanged forever (stuttering/inert behavior)
\* No actions that modify the variable after initialization
Next == UNCHANGED x

\* The complete specification with fairness (weak fairness on Next for liveness)
Spec == Init /\ [][Next]_<<x>>

\* Safety invariant: the variable is always strictly less than 1
Invariant == x < 1

\* Type invariant for completeness
TypeOK == x \in BinaryValues

\* Liveness property: the system remains stable (no progress is possible)
\* This captures that x never changes after initialization
Stable == [][x' = x]_<<x>>

\* Property that x is always in the valid range and satisfies the invariant
Safety == []Invariant

=============================================================================