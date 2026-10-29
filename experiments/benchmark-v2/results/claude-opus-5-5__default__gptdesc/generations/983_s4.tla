---------------------------- MODULE MCYoYoPruning ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo pruning specification.             *)
(* It fixes a concrete undirected graph via the operator definitions       *)
(* Nodes and Edges, declares the state variables of YoYoPruning, and       *)
(* instantiates YoYoPruning. The constants Nodes and Edges of YoYoPruning  *)
(* are substituted implicitly by the identically named definitions below,  *)
(* and the variables by the identically named variables declared here.     *)
(* Init, Next, Spec, the invariants and the liveness properties are all    *)
(* imported from YoYoPruning through the INSTANCE statement.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

\* Fixed graph used for model checking (undirected edges as 2-element sets).
Nodes == {2, 3, 4, 5, 6, 7, 8, 9, 10}

Edges == { {2,5}, {2,7}, {3,5}, {3,8}, {4,6}, {4,9},
           {5,10}, {6,10}, {7,8}, {8,9}, {9,10} }

VARIABLES active, phase, incoming, outgoing, mailbox

INSTANCE YoYoPruning
=============================================================================