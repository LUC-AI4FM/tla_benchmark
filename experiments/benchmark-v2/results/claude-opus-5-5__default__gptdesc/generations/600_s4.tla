---------------------------- MODULE MC_OptimizedCommitTS ----------------------------
(***************************************************************************)
(* Model-checking configuration for the OptimizedCommitTS protocol.        *)
(*                                                                         *)
(* This module is intended to be used with TLC. It instantiates the        *)
(* underlying protocol (defined in OptimizedCommitTS) with:                *)
(*   - three concurrent clients c1, c2, c3 (model values),                 *)
(*   - a single table with three keys 1, 2, 3,                             *)
(*   - every client using key 1 as its primary key (so the clients are     *)
(*     symmetric),                                                         *)
(*   - a symmetry set over the clients for TLC symmetry reduction.         *)
(*                                                                         *)
(* No new actions, temporal properties or proofs are defined here. Init,   *)
(* Next, Spec and the safety/liveness properties all come from the         *)
(* OptimizedCommitTS module. This file only parameterizes it.              *)
(***************************************************************************)
EXTENDS OptimizedCommitTS, TLC

\* Model values for the three concurrent clients.
CONSTANTS c1, c2, c3

\* The set of clients.
const_CLIENT == {c1, c2, c3}

\* A single table with three keys.
const_KEY == {1, 2, 3}

\* Every client may operate on every key in the table.
const_CLIENT_KEY == c1 :> {1, 2, 3} @@ c2 :> {1, 2, 3} @@ c3 :> {1, 2, 3}

\* All clients share the same primary key (1). This makes the clients symmetric.
const_CLIENT_PRIMARY == c1 :> 1 @@ c2 :> 1 @@ c3 :> 1

\* Symmetry set over the clients for TLC symmetry reduction.
symm_CLIENT == Permutations(const_CLIENT)

\* Use the protocol's own initial state, next-state relation and specification
\* for TLC (INIT/NEXT or SPECIFICATION in the .cfg file).
MC_Init == Init
MC_Next == Next
MC_Spec == Spec

(***************************************************************************)
(* Example TLC configuration (MC_OptimizedCommitTS.cfg):                   *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*     c1 = c1                                                             *)
(*     c2 = c2                                                             *)
(*     c3 = c3                                                             *)
(*     CLIENT <- const_CLIENT                                              *)
(*     KEY <- const_KEY                                                    *)
(*     CLIENT_KEY <- const_CLIENT_KEY                                      *)
(*     CLIENT_PRIMARY <- const_CLIENT_PRIMARY                              *)
(*   SYMMETRY symm_CLIENT                                                  *)
(*   SPECIFICATION MC_Spec                                                 *)
(***************************************************************************)
=============================================================================