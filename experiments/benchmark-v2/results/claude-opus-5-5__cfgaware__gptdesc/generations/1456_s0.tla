---------------------------- MODULE PossibleNamed ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

Universe == {1, 2, 3}

-----------------------------------------------------------------------------
(* Initial state: y is the full universe, x is any subset of it. *)
Init ==
    /\ y = Universe
    /\ x \in SUBSET y

(* Next-state relation: y is unchanged, x' is any subset of y'. *)
Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

-----------------------------------------------------------------------------
TypeOK ==
    /\ x \in SUBSET Universe
    /\ y \in SUBSET Universe

Inv ==
    x \subseteq y

-----------------------------------------------------------------------------
(* Named predicates whose reachability is tracked. *)

(* State predicate: x is the full set {1, 2, 3}. *)
FullSet ==
    x = {1, 2, 3}

(* Action predicate: element 3 is gained in a transition. *)
GainThree ==
    /\ 3 \notin x
    /\ 3 \in x'

(* The named predicates to be checked for possibility. *)
_POSSIBLE ==
    <<"FullSet", "GainThree">>

-----------------------------------------------------------------------------
(* Expected counts for the named predicates.
   - FullSet holds in exactly one distinct reachable state: x = {1,2,3}.
   - GainThree holds in transitions from any of the 4 subsets lacking 3
     to any of the 4 subsets containing 3: 4 * 4 = 16 transitions. *)
ExpectedFullSetCount   == Cardinality({s \in SUBSET Universe : s = Universe})
ExpectedGainThreeCount ==
    Cardinality({s \in SUBSET Universe : 3 \notin s})
      * Cardinality({t \in SUBSET Universe : 3 \in t})

ExpectedDistinctStates == Cardinality(SUBSET Universe)

(* Inspect exploration metadata via TLCGet and assert expected counts. *)
PossibleCounts ==
    LET stats == TLCGet("stats")
    IN  /\ ExpectedFullSetCount = 1
        /\ ExpectedGainThreeCount = 16
        /\ stats.distinct = ExpectedDistinctStates

=============================================================================