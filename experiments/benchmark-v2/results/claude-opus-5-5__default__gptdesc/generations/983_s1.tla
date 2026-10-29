---------------------------- MODULE MCYoYoPruning ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo leader election algorithm with     *)
(* pruning. It fixes a concrete undirected graph through the operator      *)
(* definitions Nodes and Edges, declares the state variables, and          *)
(* instantiates the module YoYoPruning. The instantiated module supplies   *)
(* the initialization predicate, transition relation, temporal formula,    *)
(* invariants, and properties. This file adds no transition relation,      *)
(* initialization predicate, specification, assumptions, or proofs.        *)
(***************************************************************************)
EXTENDS TLC

(***************************************************************************)
(* Fixed graph used for model checking. Nodes are distinct integers. Each  *)
(* undirected edge is a two-element set of nodes.                          *)
(***************************************************************************)
Nodes == {2, 3, 4, 5, 6, 7, 8, 9, 10}

Edges == { {2,5}, {2,10}, {3,4}, {3,8}, {4,5}, {4,9},
           {5,6}, {6,7}, {7,8}, {8,9}, {9,10} }

(***************************************************************************)
(* State variables of the YoYoPruning specification.                      *)
(***************************************************************************)
VARIABLES active, phase, incoming, outgoing, mailbox

(***************************************************************************)
(* Instantiate the Yo-Yo pruning specification. Nodes, Edges, and the     *)
(* variables are substituted implicitly by the identically named          *)
(* definitions and variables declared above.                               *)
(***************************************************************************)
INSTANCE YoYoPruning

=============================================================================