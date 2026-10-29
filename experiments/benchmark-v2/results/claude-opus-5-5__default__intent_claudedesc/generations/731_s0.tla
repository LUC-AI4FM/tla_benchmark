---------------------------- MODULE BoundedCounter ----------------------------
(***************************************************************************)
(* A simple demonstration / test module: a counter that starts at zero    *)
(* and increments by one on each step. Exploration is limited by a state  *)
(* constraint to states where the counter is strictly less than a         *)
(* configurable upper bound. A safety invariant asserts the same bound.   *)
(*                                                                         *)
(* For model checking, set the constant in the TLC configuration:         *)
(*     CONSTANT UpperBound = 10                                            *)
(*     INIT Init                                                           *)
(*     NEXT Next                                                           *)
(*     CONSTRAINT StateConstraint                                          *)
(*     INVARIANT TypeOK                                                    *)
(*     INVARIANT BoundInvariant                                            *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT UpperBound

ASSUME UpperBoundAssumption == UpperBound \in Nat \ {0}

\* Diagnostic label printed on startup by TLC.
ASSUME PrintT("BoundedCounter: starting model checking")

VARIABLE x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

\* State constraint: restrict exploration to states with x < UpperBound.
StateConstraint == x < UpperBound

\* Safety invariant: the counter stays strictly below the upper bound.
BoundInvariant == x < UpperBound

THEOREM Spec => [](TypeOK)
================================================================================