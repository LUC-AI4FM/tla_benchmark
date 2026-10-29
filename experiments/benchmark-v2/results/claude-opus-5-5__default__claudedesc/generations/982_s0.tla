--------------------------- MODULE MCYoYoNoPruning ---------------------------
(***************************************************************************)
(* Model-checking configuration for the Yo-Yo leader election algorithm   *)
(* without pruning. It instantiates the main specification from the       *)
(* YoYoNoPruning module with a concrete network topology.                 *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* Concrete topology: an undirected graph with five nodes and five edges. *)
(***************************************************************************)
Nodes == 1 .. 5
Edges == {{1,2}, {1,3}, {2,4}, {3,4}, {4,5}}

(***************************************************************************)
(* Alternative, larger configuration: eleven nodes and fourteen edges.    *)
(***************************************************************************)
\* Nodes == 1 .. 11
\* Edges == {{1,2}, {1,3}, {2,4}, {3,4}, {3,5}, {4,6}, {5,7}, {6,7},
\*           {6,8}, {7,9}, {8,10}, {9,10}, {9,11}, {10,11}}

(***************************************************************************)
(* Variables of the algorithm:                                            *)
(*  - phase:    the current phase of each node                            *)
(*  - incoming: neighbors with edges oriented towards the node            *)
(*  - outgoing: neighbors with edges oriented away from the node          *)
(*  - mailbox:  messages in transit between nodes                         *)
(***************************************************************************)
VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

(***************************************************************************)
(* Instantiate the main specification. The constants Nodes and Edges and  *)
(* the variables are substituted implicitly by the identically named      *)
(* definitions and variables of this module.                              *)
(***************************************************************************)
YY == INSTANCE YoYoNoPruning

(***************************************************************************)
(* Behavioral specification, delegated to YoYoNoPruning. Fairness         *)
(* conditions are part of YY!Spec.                                         *)
(***************************************************************************)
Init == YY!Init
Next == YY!Next
Spec == YY!Spec

(***************************************************************************)
(* Invariants checked by the model checker.                               *)
(***************************************************************************)
TypeOK      == YY!TypeOK
NeighborInv == YY!NeighborInv

(***************************************************************************)
(* Temporal properties checked by the model checker.                      *)
(*  - NoNewSource: a node that stops being a source never becomes one again*)
(*  - Liveness:    the algorithm eventually terminates with a leader       *)
(***************************************************************************)
NoNewSource == YY!NoNewSource
Liveness    == YY!Liveness

=============================================================================