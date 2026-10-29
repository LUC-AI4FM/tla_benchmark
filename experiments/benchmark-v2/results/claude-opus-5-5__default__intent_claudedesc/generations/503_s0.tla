------------------------------ MODULE Consensus ------------------------------
(***************************************************************************)
(* A minimal specification of the single-value consensus problem.          *)
(* The variable `chosen` is the set of values that have been chosen.       *)
(* Initially it is empty. One value from Value may be chosen, at most once. *)
(*                                                                         *)
(* Model checking note: deadlock checking must be disabled (e.g. TLC       *)
(* option -deadlock or "CHECK_DEADLOCK FALSE" in the .cfg), because the    *)
(* system legitimately stops once a value has been chosen.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Value

VARIABLE chosen

vars == <<chosen>>

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Choose == /\ chosen = {}
          /\ \E v \in Value : chosen' = {v}

Next == Choose

(* Base safety specification: no fairness. *)
Spec == Init /\ [][Next]_vars

(* Safety: validity and agreement. *)
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv

(* Liveness variant: weak fairness ensures a possible choice is eventually made. *)
LiveSpec == Spec /\ WF_vars(Next)

(* Liveness: termination. *)
Success == <>(chosen # {})

THEOREM LivenessTheorem == (Value # {}) /\ LiveSpec => Success
=============================================================================