--------------------------- MODULE MCMultiPaxos ---------------------------
(***************************************************************************)
(* Model-checking wrapper for a MultiPaxos specification.  The MultiPaxos *)
(* algorithm is defined in this module (so the file is self-contained),   *)
(* and an abstract multi-slot consensus interface, ConsensusMulti, is     *)
(* given as an inner module and instantiated with the values learned by   *)
(* MultiPaxos.  The file checks that the MultiPaxos specification         *)
(* implies the type invariant, the instantiated consensus specification,  *)
(* nontriviality and per-slot consistency.                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

-------------------------- MODULE ConsensusMulti --------------------------
(***************************************************************************)
(* Abstract multi-slot consensus: each slot can have at most one value    *)
(* chosen, and once chosen it never changes.                              *)
(***************************************************************************)
CONSTANTS CValues, CSlots
VARIABLE learned

CTypeOK == learned \in [CSlots -> SUBSET CValues]

CInit == learned = [s \in CSlots |-> {}]

CChoose(s, v) ==
    /\ learned[s] = {}
    /\ learned' = [learned EXCEPT ![s] = {v}]

CNext == \E s \in CSlots, v \in CValues : CChoose(s, v)

CSpec == CInit /\ [][CNext]_learned

CConsistency == \A s \in CSlots : Cardinality(learned[s]) <= 1
===========================================================================