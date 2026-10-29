--------------------------- MODULE MC_OptimizedCommitTS ---------------------------
(***************************************************************************)
(* TLC model-checking configuration for the OptimizedCommitTS protocol.    *)
(*                                                                         *)
(* Three concurrent clients (c1, c2, c3) operate on a single table with    *)
(* three keys. Every client uses key 1 as its primary key, so the clients  *)
(* are symmetric. Symmetry reduction over the clients is enabled.          *)
(*                                                                         *)
(* The protocol logic (variables, Init, Next, Spec, invariants) comes from *)
(* OptimizedCommitTS. This module only sets parameters, so it defines no   *)
(* actions, temporal properties or proofs of its own.                      *)
(***************************************************************************)
EXTENDS OptimizedCommitTS, TLC

\* Model-value constant declarations for the clients
CONSTANTS c1, c2, c3

\* The set of clients
CLIENT_const == {c1, c2, c3}

\* A single table with three keys
KEY_const == {1, 2, 3}

\* Each client may access every key of the table
CLIENT_KEY_const == [c \in CLIENT_const |-> {1, 2, 3}]

\* Each client uses the same primary key, 1, so the clients are symmetric
CLIENT_PRIMARY_const == [c \in CLIENT_const |-> 1]

\* Symmetry set over the clients, used by TLC for symmetry reduction
symm == Permutations(CLIENT_const)

\* Model entry points, delegated to the underlying protocol
MC_Init == Init
MC_Next == Next
MC_Spec == Spec

=============================================================================