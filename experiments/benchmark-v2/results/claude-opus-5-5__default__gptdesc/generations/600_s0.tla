---------------------------- MODULE MC_OptimizedCommitTS ----------------------------
\* This module is intended for TLC model checking only.
\* It parameterizes the OptimizedCommitTS protocol with three concurrent
\* clients (c1, c2, c3) that operate on a single table with three keys.
\* All clients share the same primary key (key 1), so the clients are
\* symmetric. This lets TLC use symmetry reduction over the client set.
\*
\* The protocol itself (Init, Next, Spec and the invariants and properties)
\* is defined in OptimizedCommitTS. This file is only a configuration and
\* parameterization layer.

EXTENDS OptimizedCommitTS, TLC

\* Model values that stand for the three clients.
CONSTANTS c1, c2, c3

\* The set of concurrent clients.
MC_CLIENT == {c1, c2, c3}

\* The single table holds three keys.
MC_KEY == {1, 2, 3}

\* Every client may touch every key in the table.
MC_CLIENT_KEY == (c1 :> MC_KEY) @@ (c2 :> MC_KEY) @@ (c3 :> MC_KEY)

\* All clients use the same primary key (1), so they are symmetric.
MC_CLIENT_PRIMARY == (c1 :> 1) @@ (c2 :> 1) @@ (c3 :> 1)

\* Symmetry set over the clients, used for TLC symmetry reduction.
MC_Symmetry == Permutations(MC_CLIENT)

\* Pass-through definitions to the underlying protocol, for the TLC config.
MC_Init == Init
MC_Next == Next
MC_Spec == Spec

=============================================================================