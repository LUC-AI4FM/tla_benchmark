---- MODULE LargeInitStateSpace ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

\* Three independent parameters drawn from distinct ranges.
\* |0..99| * |100..149| * |200..299| = 100 * 50 * 100 = 500,000 initial states
TypeOK ==
    /\ x \in 0..99
    /\ y \in 100..149
    /\ z \in 200..299

Init ==
    /\ x \in 0..99
    /\ y \in 100..149
    /\ z \in 200..299

\* The system remains static after initialization.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Trivially satisfied invariant.
Inv == TRUE

THEOREM Spec => []Inv
====