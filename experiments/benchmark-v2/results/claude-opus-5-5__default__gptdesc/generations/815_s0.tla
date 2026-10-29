---------------------------- MODULE MCParReach ----------------------------
EXTENDS ParReach, FiniteSets, Naturals

(***************************************************************************)
(* State-independent helper definitions for model checking ParReach.       *)
(* This module declares no variables, actions or temporal properties.      *)
(* Init, Next and Spec are inherited from ParReach and are not redefined.  *)
(***************************************************************************)

\* A successor function in which every node has exactly two successors.
MCSucc ==
  CHOOSE f \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(f[n]) = 2

\* All sequences over S whose length is between 0 and Cardinality(Nodes).
MCSeq(S) ==
  UNION { [1..n -> S] : n \in 0..Cardinality(Nodes) }

=============================================================================