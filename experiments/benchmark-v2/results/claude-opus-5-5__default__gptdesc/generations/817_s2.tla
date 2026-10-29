------------------------------ MODULE ReachableHelpers ------------------------------
(***************************************************************************)
(* A small structural helper module built on top of the Reachable module.  *)
(* It defines two operators:                                               *)
(*                                                                         *)
(*  - TwoSuccFn: a successor function from Nodes to subsets of Nodes in   *)
(*    which every node has exactly two successors (chosen with CHOOSE).    *)
(*                                                                         *)
(*  - BoundedSeqs(S): the set of finite sequences over an arbitrary set S  *)
(*    whose length is at most the cardinality of Nodes.                    *)
(*                                                                         *)
(* This module declares no variables or actions and adds no temporal       *)
(* specification of its own. The CONSTANTS, VARIABLES, Init, Next and      *)
(* Spec all come from the imported Reachable module.                       *)
(***************************************************************************)
EXTENDS Reachable, Naturals, FiniteSets, Sequences

(***************************************************************************)
(* A successor function in which every node has exactly two successors.   *)
(***************************************************************************)
TwoSuccFn ==
    CHOOSE f \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(f[n]) = 2

(***************************************************************************)
(* All finite sequences over S whose length is bounded by |Nodes|.         *)
(***************************************************************************)
BoundedSeqs(S) ==
    UNION { [1..k -> S] : k \in 0..Cardinality(Nodes) }

=============================================================================