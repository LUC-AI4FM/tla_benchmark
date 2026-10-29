------------------------------ MODULE MCMultiPaxos ------------------------------
(***************************************************************************)
(* Model-checking wrapper around a MultiPaxos specification.  The         *)
(* underlying MultiPaxos protocol is defined below, followed by the       *)
(* checking operators: a type invariant, an instantiation of the abstract *)
(* ConsensusMulti specification (refinement mapping chosen <- learned),   *)
(* and the invariants Nontriviality and per-slot Consistency.             *)
(*                                                                         *)
(* NOTE: checking Spec => C!Spec (refinement) and the type invariant is   *)
(* only feasible for very small constants (e.g. 2 acceptors, 2 values,    *)
(* MaxBallot = 1, MaxSlot = 1) because of state-space blowup.  The        *)
(* simpler invariants Nontriviality and Consistency can be checked on     *)
(* larger instances.                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

    ---------------------------- MODULE ConsensusMulti ----------------------------
    (***********************************************************************)
    (* Abstract multi-slot consensus: each slot chooses at most one value. *)
    (***********************************************************************)
    EXTENDS Naturals, FiniteSets
    CONSTANTS CSlots, CValues
    VARIABLE chosen

    CTypeOK == chosen \in [CSlots -> SUBSET CValues]

    CInit == chosen = [s \in CSlots |-> {}]

    Choose(s, v) ==
        /\ chosen[s] = {}
        /\ chosen' = [chosen EXCEPT ![s] = {v}]

    CNext == \E s \in CSlots, v \in CValues : Choose(s, v)

    CSpec == CInit /\ [][CNext]_chosen
    ===============================================================================