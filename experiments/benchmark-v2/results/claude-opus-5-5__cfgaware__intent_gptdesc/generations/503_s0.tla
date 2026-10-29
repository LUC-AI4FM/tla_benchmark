---------------------------- MODULE Consensus ----------------------------
(***************************************************************************)
(* Abstract specification of the consensus problem.                        *)
(*                                                                         *)
(* A set of processes must agree on a single value taken from the          *)
(* parameter set Values.  Communication details are abstracted away.       *)
(* Values may be proposed, and one proposed value may become chosen        *)
(* (learned).  The model records:                                          *)
(*   proposed : the set of values proposed so far                          *)
(*   chosen   : the set of chosen values (empty, or a singleton)           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Values

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

---------------------------------------------------------------------------
(* Type invariant.  It also implies validity: chosen \subseteq Values.    *)
TypeOK == /\ proposed \subseteq Values
          /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

---------------------------------------------------------------------------
(* Initially nothing has been proposed and nothing has been chosen.       *)
Init == /\ proposed = {}
        /\ chosen = {}

(* A process proposes some value from the allowed set.                     *)
Propose(v) == /\ v \in Values
              /\ v \notin proposed
              /\ proposed' = proposed \cup {v}
              /\ UNCHANGED chosen

(* Learn/choose event: if nothing has been chosen yet, a single proposed   *)
(* value becomes chosen.  This transition can happen at most once.         *)
Choose == /\ chosen = {}
          /\ \E v \in proposed : chosen' = {v}
          /\ UNCHANGED proposed

(* Once a value is chosen the system is finished; this step only stutters *)
(* and exists so that terminated executions are not reported as deadlock. *)
Done == /\ chosen # {}
        /\ UNCHANGED vars

Next == \/ \E v \in Values : Propose(v)
        \/ Choose
        \/ Done

Spec == Init /\ [][Next]_vars

(* Liveness: weak fairness — an action continuously enabled is eventually *)
(* taken.  Hence some value is eventually proposed and then chosen.        *)
LiveSpec == Spec /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Safety properties                                                       *)

(* (1) Validity: any chosen value comes from Values and was proposed.      *)
Validity == chosen \subseteq Values /\ chosen \subseteq proposed

(* (2) Agreement: at most one value is ever chosen.                        *)
ConsistencyInv == Cardinality(chosen) <= 1

(* (3) Integrity: once a value is chosen it never changes.                 *)
Integrity == [][chosen # {} => chosen' = chosen]_vars

(* (5) Nontriviality: nothing can be chosen unless it was proposed;        *)
(* in particular, if no value has been proposed, nothing is chosen.        *)
NonTriviality == proposed = {} => chosen = {}

---------------------------------------------------------------------------
(* Liveness property                                                       *)

(* (4) Eventual choice: some value from Values is eventually chosen.       *)
Success == <>(chosen # {})

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Validity /\ ConsistencyInv /\ NonTriviality)
THEOREM Spec => Integrity
THEOREM (Values # {}) => (LiveSpec => Success)
=============================================================================