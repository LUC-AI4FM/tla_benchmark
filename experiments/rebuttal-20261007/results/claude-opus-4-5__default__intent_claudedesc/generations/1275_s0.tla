---------------------------- MODULE ConstrainedInit ----------------------------
EXTENDS Integers

VARIABLES x

\* Type invariant: x is an integer in the range 0..1
TypeOK == x \in 0..1

\* Initialization predicate:
\* x is chosen nondeterministically from {0, 1} but must also be strictly less than 1.
\* The conjunction of x \in 0..1 and x < 1 forces x = 0.
Init == 
    /\ x \in 0..1
    /\ x < 1

\* Next state relation:
\* After initialization, the variable remains unchanged (stuttering only).
Next == UNCHANGED x

\* The complete specification with weak fairness (though trivial here since Next only stutters)
Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Safety invariant: x is always strictly less than 1
\* This should hold in all reachable states given our constrained initialization
InvariantLessThanOne == x < 1

\* Additional invariant: x is always exactly 0
\* This follows from the initialization constraint
InvariantZero == x = 0

\* Liveness property: x remains 0 forever (trivially true since x never changes)
AlwaysZero == []InvariantZero

================================================================================