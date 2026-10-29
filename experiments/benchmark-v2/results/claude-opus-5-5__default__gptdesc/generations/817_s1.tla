---------------------------- MODULE MCReachableHelpers ----------------------------
(***************************************************************************)
(* A small structural helper module over the Reachable module.  It adds   *)
(* no variables, actions, temporal formulas or proofs.  The constants      *)
(* (Nodes, succ, root), the variables, and Init, Next and Spec all come    *)
(* from the extended Reachable module.  This module only adds two helper   *)
(* operators.                                                             *)
(***************************************************************************)
EXTENDS Reachable, Integers, FiniteSets, Sequences

(***************************************************************************)
(* A successor function from Nodes to subsets of Nodes in which every     *)
(* node has exactly two successors.                                        *)
(***************************************************************************)
SuccSet2 ==
  CHOOSE f \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(f[n]) = 2

(***************************************************************************)
(* The set of finite sequences over an arbitrary set S whose lengths are  *)
(* at most the cardinality of Nodes.                                       *)
(***************************************************************************)
BoundedSeq(S) ==
  UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

==================================================================================