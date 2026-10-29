---------------------------- MODULE PossibleSubset ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, U

vars == <<x, U>>

Universe == {1, 2, 3}

\* The initial subset is drawn from a proper subcollection of the universe.
Init == /\ U = Universe
        /\ x \in SUBSET {1, 2}

\* Any next subset of the universe is allowed. The universe never changes.
Next == /\ x' \in SUBSET U
        /\ U' = U

Spec == Init /\ [][Next]_vars

\* Type correctness
TypeOK == /\ U = Universe
          /\ x \in SUBSET Universe

\* Safety: the subset is always contained in the universe.
Inv == x \subseteq U

\* The universe value never changes.
UniverseConstant == [][U' = U]_vars

\* Named predicates whose occurrences can be counted or checked.
FullSet == x = U

GainThree == /\ 3 \notin x
             /\ 3 \in x'

\* The negations below are invariants and properties that are expected to be
\* violated. Each violation witnesses that the predicate can occur.
FullSetUnreachable == ~FullSet
NeverGainThree == [][~GainThree]_vars

\* Possibility witness: a state predicate that holds in every reachable state.
\* The checks for the named predicates FullSet and GainThree are expressed by
\* the witness formulas above.
_POSSIBLE == /\ x \subseteq U
             /\ U = Universe

\* Count check: there are 4 initial states and 8 reachable distinct states.
\* There must be at least one reachable state.
PossibleCounts == /\ Cardinality(SUBSET {1, 2}) = 4
                  /\ Cardinality(SUBSET Universe) = 8
                  /\ TLCGet("distinct") >= 1

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => UniverseConstant
===============================================================================