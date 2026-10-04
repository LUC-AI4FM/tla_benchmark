---------------------------- MODULE Specification ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Universe

VARIABLES subset, universe

vars == <<subset, universe>>

\* The three-element universe
UniverseSet == {1, 2, 3}

\* A proper subcollection of the universe (not empty, not the full set)
ProperSubcollection == {S \in SUBSET UniverseSet : S /= {} /\ S /= UniverseSet}

\* Type invariant
TypeOK == 
    /\ subset \in SUBSET UniverseSet
    /\ universe = UniverseSet

\* Initial state: subset is contained in a proper subcollection, universe is the three-element set
Init == 
    /\ subset \in ProperSubcollection
    /\ universe = UniverseSet

\* Transition: subset can change to any subset of universe, universe never changes
Next == 
    /\ subset' \in SUBSET universe
    /\ universe' = universe

\* Safety: subset is always a subset of universe
SubsetSafety == subset \subseteq universe

\* Invariance of universe: universe value never changes (captured by universe = UniverseSet)
UniverseInvariant == universe = UniverseSet

\* Main invariant combining safety properties
Inv == 
    /\ TypeOK
    /\ SubsetSafety
    /\ UniverseInvariant

\* Predicate: full set is reached (subset equals universe)
FullSetReached == subset = universe

\* Predicate: element 3 is gained in a transition
\* This is a state predicate that can be used with Next to check if element 3 was added
Element3Gained == 
    /\ 3 \notin subset
    /\ 3 \in subset'

\* Action predicate for gaining element 3
GainElement3 == 
    /\ 3 \notin subset
    /\ 3 \in subset'
    /\ subset' \in SUBSET universe
    /\ universe' = universe

\* Predicate to check if we're in a state where element 3 is not present
NotContains3 == 3 \notin subset

\* Predicate to check if we're in a state where element 3 is present
Contains3 == 3 \in subset

\* Temporal property: it's possible to reach the full set
\* (This would be violated if we want to show reachability - use as a check)
NeverFull == []~FullSetReached

\* Temporal property: eventually full set is reached (may not hold from all states)
EventuallyFull == <>FullSetReached

\* Fairness condition for reasoning about liveness
Fairness == WF_vars(Next)

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars

\* Specification with fairness for liveness checking
FairSpec == Spec /\ Fairness

=============================================================================