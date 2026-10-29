---------------------------- MODULE MCReachable ----------------------------
(***************************************************************************)
(* A small structural helper module built on top of the Reachable module. *)
(* It defines two operators:                                              *)
(*                                                                         *)
(*   - SuccWithTwoSuccessors: a successor function chosen from            *)
(*     [Nodes -> SUBSET Nodes] in which every node has exactly two        *)
(*     successors.                                                         *)
(*                                                                         *)
(*   - SeqOf(S): the set of finite sequences over an arbitrary set S      *)
(*     whose lengths are at most Cardinality(Nodes).                      *)
(*                                                                         *)
(* The module declares no variables, actions, temporal specification, or  *)
(* proofs. It is not a complete transition-system specification, so it    *)
(* has no Init, Next or Spec.                                              *)
(***************************************************************************)
EXTENDS Reachable, Integers, Sequences, FiniteSets

(***************************************************************************)
(* A successor function on Nodes in which every node has exactly two      *)
(* successors.                                                             *)
(***************************************************************************)
SuccWithTwoSuccessors ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

(***************************************************************************)
(* The set of finite sequences over S whose length is bounded by the      *)
(* number of nodes.                                                        *)
(***************************************************************************)
SeqOf(S) == UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================