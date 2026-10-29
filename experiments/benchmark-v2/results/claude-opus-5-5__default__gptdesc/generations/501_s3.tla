------------------------------ MODULE MCMultiPaxos ------------------------------
(***************************************************************************)
(* Model-checking wrapper around a MultiPaxos specification.  The         *)
(* MultiPaxos algorithm is included here so the module is self-contained. *)
(* The wrapper adds a type-correctness invariant and consensus-oriented    *)
(* checking operators over the MultiPaxos state.  It instantiates a        *)
(* separate ConsensusMulti specification to compare the learned values     *)
(* against an abstract multi-slot consensus interface.                     *)
(*                                                                         *)
(* NOTE: Checking the refinement Spec => CM!Spec is feasible only for      *)
(* very small constant instances (for example 2 acceptors, 2 values,       *)
(* 2 ballots, 1-2 slots) because of state-space blowup.  The simpler       *)
(* invariants (TypeOK, Nontriviality, Consistency) can be checked on       *)
(* somewhat larger instances.                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

  ----------------------------- MODULE ConsensusMulti -----------------------------
  (*************************************************************************)
  (* Abstract multi-slot consensus: for every slot, at most one value is  *)
  (* ever chosen, and once chosen it never changes.                       *)
  (*************************************************************************)
  EXTENDS FiniteSets
  CONSTANTS CValues, CSlots
  VARIABLE chosen

  CTypeOK == chosen \in [CSlots -> SUBSET CValues]

  CInit == chosen = [s \in CSlots |-> {}]

  CChoose(s, v) ==
      /\ chosen[s] = {}
      /\ chosen' = [chosen EXCEPT ![s] = {v}]

  CNext == \E s \in CSlots, v \in CValues : CChoose(s, v)

  CSpec == CInit /\ [][CNext]_chosen

  CInv == \A s \in CSlots : Cardinality(chosen[s]) <= 1
  ==================================================================================