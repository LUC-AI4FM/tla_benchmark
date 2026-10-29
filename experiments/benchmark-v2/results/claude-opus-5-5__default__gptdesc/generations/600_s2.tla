---------------------------- MODULE MC_OptimizedCommitTS ----------------------------
(***************************************************************************)
(* Model-checking configuration for the OptimizedCommitTS protocol.        *)
(*                                                                         *)
(* Three concurrent clients (c1, c2, c3) operate on a single table with    *)
(* three keys. Every client uses key 1 as its primary key, so the clients  *)
(* are symmetric. TLC can therefore apply symmetry reduction over the set  *)
(* of clients.                                                             *)
(*                                                                         *)
(* This module only parameterizes the underlying protocol. The variables,  *)
(* Init, Next, Spec, invariants and any liveness or fairness conditions    *)
(* all come from OptimizedCommitTS.                                        *)
(***************************************************************************)
EXTENDS OptimizedCommitTS, TLC

\* Model values that represent the clients.
CONSTANTS c1, c2, c3

\* Value for the CLIENT constant: three concurrent clients.
const_CLIENT == {c1, c2, c3}

\* Value for the KEY constant: one table with three keys.
const_KEY == {1, 2, 3}

\* Value for the CLIENT_KEY constant: each client may access all keys.
const_CLIENT_KEY == c1 :> {1, 2, 3} @@ c2 :> {1, 2, 3} @@ c3 :> {1, 2, 3}

\* Value for the CLIENT_PRIMARY constant: all clients share primary key 1.
const_CLIENT_PRIMARY == c1 :> 1 @@ c2 :> 1 @@ c3 :> 1

\* Symmetry set over the clients, used by TLC for symmetry reduction.
symm_clients == Permutations(const_CLIENT)

\* Specification and properties re-exported for the TLC configuration.
MC_Init == Init
MC_Next == Next
MC_Spec == Spec

=============================================================================