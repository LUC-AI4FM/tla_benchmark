------------------------------- MODULE BFSModelChecker -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Abstract reachability specification.  A set of explored nodes grows by  *)
(* one node at a time.  Each added node is either initial or a successor   *)
(* of an already explored node.                                            *)
(***************************************************************************)
---------------------------- MODULE MCReachability ----------------------------
CONSTANTS RNodes, RInitNodes, RSuccs
VARIABLE explored

RTypeOK == explored \subseteq RNodes

RInit == explored = {}

RNext ==
    \E n \in RNodes \ explored :
        /\ \/ n \in RInitNodes
           \/ \E m \in explored : n \in RSuccs[m]
        /\ explored' = explored \cup {n}

RSpec == RInit /\ [][RNext]_explored
===============================================================================