---------------------------- MODULE MCReachable ----------------------------
(***************************************************************************)
(* Helper module for model checking the Reachable specification.           *)
(*                                                                         *)
(* It defines two helper operators over the constants and data structures  *)
(* provided by the imported Reachable module:                              *)
(*                                                                         *)
(*   SuccVal       - a successor function mapping each node to a set of    *)
(*                   nodes, chosen so that every node has exactly two      *)
(*                   successors.                                           *)
(*                                                                         *)
(*   BoundedSeq(S) - the set of finite sequences over an arbitrary set S   *)
(*                   whose lengths are at most Cardinality(Nodes).         *)
(*                                                                         *)
(* This module declares no variables, actions or temporal formulas of its  *)
(* own. Init, Next and Spec are the ones inherited from Reachable, so they *)
(* are not redefined here. Redefining them would be a multiple-definition  *)
(* error in SANY.                                                          *)
(***************************************************************************)
EXTENDS Reachable, Integers, Sequences, FiniteSets

(***************************************************************************)
(* A successor function from Nodes to subsets of Nodes in which every node *)
(* has exactly two successors.                                             *)
(***************************************************************************)
SuccVal ==
    CHOOSE f \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(f[n]) = 2

(***************************************************************************)
(* The set of all finite sequences over S whose length is bounded by the   *)
(* number of nodes.                                                        *)
(***************************************************************************)
BoundedSeq(S) ==
    UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================