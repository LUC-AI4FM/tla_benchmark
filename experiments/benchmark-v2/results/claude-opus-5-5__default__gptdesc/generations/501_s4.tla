------------------------------- MODULE MC_MultiPaxos -------------------------------
(***************************************************************************)
(* Model-checking wrapper around a MultiPaxos specification.              *)
(*                                                                         *)
(* The underlying MultiPaxos protocol state (maxBal, maxVBal, maxVal,      *)
(* msgs) is defined below.  On top of it this module defines a type        *)
(* invariant and consensus-oriented checking operators.  It also           *)
(* instantiates an abstract ConsensusMulti specification and maps the      *)
(* values learned by MultiPaxos onto that interface.                       *)
(*                                                                         *)
(* NOTE: Checking the refinement  Spec => CM!Spec  is only feasible for    *)
(* very small constant instances (e.g. 3 acceptors, 2 values, 2 slots,     *)
(* MaxBallot = 1) because of state-space blowup.  The simpler invariants   *)
(* TypeOK, Nontriviality and Consistency can be checked on larger          *)
(* instances.                                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors,   \* set of acceptors
          Values,      \* set of values that can be proposed
          Quorums,     \* set of quorums (subsets of Acceptors)
          Slots,       \* set of log slots (instances of consensus)
          MaxBallot    \* largest ballot number

ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME MaxBallot \in Nat

Ballots == 0..MaxBallot

None == CHOOSE v : v \notin Values

---------------------------- MODULE ConsensusMulti ----------------------------
(***************************************************************************)
(* Abstract consensus interface for a sequence of slots: in each slot at  *)
(* most one value is ever chosen, and once chosen it never changes.        *)
(***************************************************************************)
CONSTANTS Values, Slots

VARIABLE chosen

CTypeOK == chosen \in [Slots -> SUBSET Values]

CInit == chosen = [s \in Slots |-> {}]

Choose(s, v) ==
    /\ chosen[s] = {}
    /\ chosen' = [chosen EXCEPT ![s] = {v}]

CNext == \E s \in Slots, v \in Values : Choose(s, v)

Spec == CInit /\ [][CNext]_chosen
===============================================================================