---------------------------- MODULE SubsetUniverse ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES S, U

vars == <<S, U>>

Universe == {1, 2, 3}

\* A proper subcollection of the universe that bounds the initial subset
InitBound == {1, 2}

-----------------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ U = Universe
    /\ S \in SUBSET Universe

-----------------------------------------------------------------------------
Init ==
    /\ U = Universe
    /\ S \in SUBSET InitBound

\* Any next subset of the universe is allowed, regardless of the current subset.
\* The universe never changes.
Next ==
    /\ S' \in SUBSET U
    /\ U' = U

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Named predicates for counting reachable states and transitions

\* State predicate: the full set has been reached
FullSetReached == S = U

\* Action predicate: element e is gained in a step
ElementGained(e) == e \notin S /\ e \in S'

\* Action predicate: element 3 is gained in a step
Element3Gained == ElementGained(3)

-----------------------------------------------------------------------------
\* Safety: the subset is always a subset of the universe
SubsetSafety == S \subseteq U

SafetyProperty == []SubsetSafety

\* Invariance of the universe: the universe never changes
UniverseConstant == U = Universe

UniverseUnchanged == [][U' = U]_vars

UniverseInvariance == []UniverseConstant /\ UniverseUnchanged

\* Reachability of the full set.
\* Checked as an invariant that is EXPECTED TO BE VIOLATED:
\* a counterexample trace witnesses that S = U is reachable.
NeverFull == ~FullSetReached

\* Existence of a transition that adds element 3.
\* Checked as an action property that is EXPECTED TO BE VIOLATED:
\* a counterexample trace witnesses a step from 3 \notin S to 3 \in S'.
NeverGain3 == [][~Element3Gained]_vars

\* General form for any element
NeverGain(e) == [][~ElementGained(e)]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => SafetyProperty
THEOREM Spec => UniverseInvariance

=============================================================================