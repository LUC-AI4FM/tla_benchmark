---------------------------- MODULE MCParReach ----------------------------
(***************************************************************************)
(* A purely structural extension of the ParReach module.                   *)
(* It adds two state-independent helper definitions:                      *)
(*                                                                         *)
(*   MCSuccFunction : a successor function from Nodes to subsets of Nodes  *)
(*                    in which every node has exactly two successors.      *)
(*                                                                         *)
(*   MCBoundedSeq(S): the set of all sequences over S whose length lies in *)
(*                    0 .. Cardinality(Nodes).                             *)
(*                                                                         *)
(* This module declares no variables, no actions and no temporal           *)
(* properties of its own.  CONSTANTS, VARIABLES, Init, Next and Spec are   *)
(* all inherited from ParReach.                                            *)
(***************************************************************************)
EXTENDS ParReach, FiniteSets, Naturals, Sequences

(***************************************************************************)
(* A successor function in which every node has exactly two successors.    *)
(***************************************************************************)
MCSuccFunction ==
    CHOOSE f \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(f[n]) = 2

(***************************************************************************)
(* The set of sequences over S of length 0 through Cardinality(Nodes).     *)
(***************************************************************************)
MCBoundedSeq(S) ==
    UNION { [1 .. len -> S] : len \in 0 .. Cardinality(Nodes) }

=============================================================================