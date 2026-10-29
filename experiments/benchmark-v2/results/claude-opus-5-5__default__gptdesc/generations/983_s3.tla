--------------------------- MODULE MCYoYoPruning ---------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo pruning specification.             *)
(* It fixes a concrete graph through the operators Nodes and Edges,        *)
(* declares the state variables used by YoYoPruning, and instantiates      *)
(* that module. Init, Next, Spec, the type and safety invariants, and the  *)
(* liveness properties all come from YoYoPruning through the unnamed       *)
(* INSTANCE below. This file does not define them itself.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Fixed, connected, undirected graph used for model checking.             *)
(* Each node is a natural number, and each edge is a 2-element set.        *)
(***************************************************************************)
Nodes == {2, 3, 5, 7, 8, 9, 11}

Edges == { {2, 3}, {2, 5}, {3, 5}, {3, 7}, {5, 8},
           {7, 9}, {8, 9}, {8, 11}, {9, 11} }

(***************************************************************************)
(* State variables of the Yo-Yo pruning algorithm.                         *)
(***************************************************************************)
VARIABLES active, phase, incoming, outgoing, mailbox

(***************************************************************************)
(* Instantiate the algorithm. The constants Nodes and Edges and the        *)
(* variables above are substituted implicitly by name.                     *)
(***************************************************************************)
INSTANCE YoYoPruning

=============================================================================