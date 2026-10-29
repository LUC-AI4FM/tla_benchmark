---------------------------- MODULE MCYoYoPruning ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo pruning specification.             *)
(* It fixes a concrete undirected graph through the operators Nodes and    *)
(* Edges, declares the state variables of the algorithm, and instantiates  *)
(* the module YoYoPruning. The instantiated module supplies Init, Next,    *)
(* Spec, the type and safety invariants, and the liveness properties.      *)
(***************************************************************************)
EXTENDS TLC, Naturals, FiniteSets

(***************************************************************************)
(* Fixed graph used for model checking.                                    *)
(***************************************************************************)
Nodes == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

Edges == { {1, 2}, {1, 9}, {2, 3}, {3, 4}, {3, 5},
           {3, 6}, {6, 7}, {6, 8}, {9, 10} }

(***************************************************************************)
(* State variables of the Yo-Yo pruning algorithm.                         *)
(***************************************************************************)
VARIABLES active, phase, incoming, outgoing, mailbox

(***************************************************************************)
(* Instantiate the algorithm. Nodes, Edges and the variables are           *)
(* substituted implicitly by the identically named definitions above.      *)
(* All definitions of YoYoPruning (Init, Next, Spec, invariants and        *)
(* liveness properties) become available in this module.                   *)
(***************************************************************************)
INSTANCE YoYoPruning

=============================================================================