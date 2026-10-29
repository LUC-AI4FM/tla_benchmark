---------------------------- MODULE NamedPredicates ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT S

ASSUME S = {1, 2, 3}

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in SUBSET S
    /\ y \in SUBSET S

Init ==
    /\ y = S
    /\ x \in SUBSET y

Next ==
    /\ y' = y
    /\ x' \in SUBSET y'

(* The description says there is no full temporal Spec operator.            *)
(* This one is included only because the output format requires a Spec.     *)
(* It has no fairness condition.                                             *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Named predicates                                                          *)

FullSet == x = {1, 2, 3}

GainThree == /\ 3 \notin x
             /\ 3 \in x'

-----------------------------------------------------------------------------
(* Expected counts for the named predicates, computed over the reachable     *)
(* state space (y is fixed to S, x ranges over SUBSET S).                    *)

ReachableX == SUBSET S

FullSetCount == Cardinality({s \in ReachableX : s = {1, 2, 3}})

GainThreeCount ==
    Cardinality({ <<s, t>> \in ReachableX \X ReachableX :
                      /\ 3 \notin s
                      /\ 3 \in t })

ExpectedFullSetCount   == 1
ExpectedGainThreeCount == 16
ExpectedDistinctStates == 8

(* Exploration-metadata check, intended for use as a POSTCONDITION.          *)
PostCondition ==
    /\ Assert(FullSetCount = ExpectedFullSetCount,
              <<"FullSet count mismatch", FullSetCount>>)
    /\ Assert(GainThreeCount = ExpectedGainThreeCount,
              <<"GainThree count mismatch", GainThreeCount>>)
    /\ Assert(TLCGet("distinct") = ExpectedDistinctStates,
              <<"distinct state count mismatch", TLCGet("distinct")>>)

-----------------------------------------------------------------------------
(* Safety invariants                                                         *)

YUnchanged == y = S

XSubsetY == x \subseteq y

Invariants == TypeOK /\ YUnchanged /\ XSubsetY

=============================================================================