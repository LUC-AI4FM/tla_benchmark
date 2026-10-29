---------------------------- MODULE MCReachable ----------------------------
(***************************************************************************)
(* A small structural helper module over the imported Reachable module.    *)
(* It defines two operators:                                               *)
(*   - SuccSet: a successor function from Nodes to subsets of Nodes in     *)
(*     which every node has exactly two successors.                        *)
(*   - BoundedSeq(S): the set of finite sequences over S whose lengths     *)
(*     are at most Cardinality(Nodes).                                     *)
(* As described, it declares no variables, actions, temporal spec, or      *)
(* proofs. Init, Next and Spec are therefore not included.                 *)
(***************************************************************************)
EXTENDS Reachable, Integers, Sequences, FiniteSets

(***************************************************************************)
(* A successor function in which every node has exactly two successors.    *)
(***************************************************************************)
SuccSet ==
    CHOOSE succ \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(succ[n]) = 2

(***************************************************************************)
(* The set of sequences over S with length bounded by Cardinality(Nodes).  *)
(***************************************************************************)
BoundedSeq(S) ==
    UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================