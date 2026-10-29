---------------------------- MODULE MCYoYoPruning ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo pruning specification.             *)
(* It fixes a concrete graph through the operator definitions Nodes and    *)
(* Edges, declares the state variables, and instantiates YoYoPruning.      *)
(* The initial predicate, next-state relation, temporal specification,     *)
(* invariants and liveness properties (Init, Next, Spec, ...) are all      *)
(* imported from the instantiated module YoYoPruning.                      *)
(***************************************************************************)
EXTENDS TLC

Nodes == {1,2,3,4,5,6,7,8,9,10}

Edges == { {1,2}, {1,9}, {2,3}, {3,4}, {3,5}, {3,6}, {4,5}, {4,8},
           {5,6}, {6,7}, {6,9}, {7,8}, {8,10}, {9,10} }

VARIABLES active, phase, incoming, outgoing, mailbox

INSTANCE YoYoPruning

=============================================================================