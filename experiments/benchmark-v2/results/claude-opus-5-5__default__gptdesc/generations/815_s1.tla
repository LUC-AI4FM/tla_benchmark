---------------------------- MODULE MCParReach ----------------------------
(***************************************************************************)
(* Structural extension of the ParReach module.  It adds two state-        *)
(* independent helper definitions used for model checking:                 *)
(*                                                                         *)
(*   MCSucc    - a successor function from Nodes to subsets of Nodes in    *)
(*               which every node has exactly two successors.              *)
(*                                                                         *)
(*   MCSeq(S)  - the set of all sequences over S whose length ranges from  *)
(*               0 up to Cardinality(Nodes).                               *)
(*                                                                         *)
(* This module declares no variables, no actions, and no temporal          *)
(* properties of its own.  The constants, variables, Init, Next, Spec and  *)
(* all properties are those of ParReach, inherited through EXTENDS.        *)
(***************************************************************************)
EXTENDS ParReach, FiniteSets, Naturals

MCSucc ==
    CHOOSE sr \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(sr[n]) = 2

MCSeq(S) ==
    UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================