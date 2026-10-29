---------------------------- MODULE NamedStateCounts ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS None

VARIABLES x, y

vars == <<x, y>>

U == {1, 2, 3}

-----------------------------------------------------------------------------
(* Initial state: y is the full universe; x is any subset of y.               *)
-----------------------------------------------------------------------------
Init ==
    /\ y \in {U}
    /\ x \in SUBSET y

-----------------------------------------------------------------------------
(* Next-state relation: y is left unchanged and x' is a subset of y'.         *)
-----------------------------------------------------------------------------
Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Named predicates.                                                         *)
-----------------------------------------------------------------------------

\* State predicate: x is the full set {1, 2, 3}.
FullSet == x = {1, 2, 3}

\* Action predicate: element 3 is gained in a transition.
GainThree == 3 \notin x /\ 3 \in x'

-----------------------------------------------------------------------------
(* Type and safety invariants.                                               *)
-----------------------------------------------------------------------------
TypeOK ==
    /\ y = U
    /\ x \subseteq U

SubsetInv == x \subseteq y

-----------------------------------------------------------------------------
(* Expected counts for the named predicates, computed over the reachable     *)
(* state space and transition relation.                                      *)
-----------------------------------------------------------------------------
ReachableStates == { <<s, U>> : s \in SUBSET U }

FullSetStates == { st \in ReachableStates : st[1] = {1, 2, 3} }

GainThreeTransitions ==
    { <<a, b>> \in (SUBSET U) \X (SUBSET U) : 3 \notin a /\ 3 \in b }

ExpectedDistinct  == 8
ExpectedFullSet   == 1
ExpectedGainThree == 16

ASSUME Cardinality(ReachableStates) = ExpectedDistinct
ASSUME Cardinality(FullSetStates) = ExpectedFullSet
ASSUME Cardinality(GainThreeTransitions) = ExpectedGainThree

-----------------------------------------------------------------------------
(* Exploration metadata via TLCGet, checked after model checking completes.  *)
-----------------------------------------------------------------------------
PostCondition ==
    LET stats == TLCGet("stats")
    IN  /\ stats.distinct = ExpectedDistinct
        /\ Cardinality(FullSetStates) = ExpectedFullSet
        /\ Cardinality(GainThreeTransitions) = ExpectedGainThree

=============================================================================