---------------------------- MODULE MCParReach ----------------------------
(***************************************************************************)
(* Structural extension of the ParReach module.  It introduces no new      *)
(* variables, actions, or temporal properties.  The variables, Init, Next, *)
(* Spec, invariants and liveness properties all come from ParReach.        *)
(* It only adds two state-independent mathematical definitions that are    *)
(* useful for model checking.                                              *)
(***************************************************************************)
EXTENDS ParReach, FiniteSets, Naturals, Sequences

(***************************************************************************)
(* A successor function in which every node has exactly two successors.    *)
(***************************************************************************)
MCSucc ==
  CHOOSE sr \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(sr[n]) = 2

(***************************************************************************)
(* The set of sequences over S whose length is between 0 and the number    *)
(* of nodes.  This is a finite replacement for Seq(S).                     *)
(***************************************************************************)
MCSeq(S) == UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================