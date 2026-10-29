---------------------------- MODULE MCParReach ----------------------------
(***************************************************************************)
(* Structural extension of the ParReach module that adds two              *)
(* state-independent helper definitions, used for model checking:         *)
(*                                                                         *)
(*   MCSucc    : a successor function from Nodes to subsets of Nodes in   *)
(*               which every node has exactly two successors.              *)
(*                                                                         *)
(*   MCSeq(S)  : the set of all sequences over S whose length is between  *)
(*               0 and Cardinality(Nodes), inclusive.                      *)
(*                                                                         *)
(* This module declares no variables, actions or temporal properties of   *)
(* its own. Init, Next, Spec and the properties come from ParReach, so    *)
(* they are not redefined here, because redefining them would fail SANY.  *)
(***************************************************************************)
EXTENDS ParReach, FiniteSets, Naturals, Sequences, TLC

MCSucc ==
    CHOOSE f \in [Nodes -> SUBSET Nodes] :
        \A n \in Nodes : Cardinality(f[n]) = 2

MCSeq(S) ==
    UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================