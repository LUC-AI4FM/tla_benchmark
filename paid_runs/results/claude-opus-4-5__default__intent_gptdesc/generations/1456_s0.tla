-------------------------------- MODULE MutableSubset --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS E1, E2, E3

VARIABLES subset, universe

\* The fixed three-element universe
Universe == {E1, E2, E3}

\* A proper subcollection for initial constraint (non-empty, proper subset of Universe)
InitialSubcollections == {S \in SUBSET Universe : S /= {} /\ S /= Universe}

\* Type invariant
TypeOK ==
    /\ subset \in SUBSET Universe
    /\ universe = Universe

\* Initial state: subset is contained in some proper subcollection, universe is fixed
Init ==
    /\ subset \in UNION {SUBSET S : S \in InitialSubcollections}
    /\ universe = Universe

\* Next state: subset can change to any subset of universe, universe stays fixed
Next ==
    /\ subset' \in SUBSET universe
    /\ UNCHANGED universe

\* Specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_<<subset, universe>> /\ WF_<<subset, universe>>(Next)

\* =============================================================================