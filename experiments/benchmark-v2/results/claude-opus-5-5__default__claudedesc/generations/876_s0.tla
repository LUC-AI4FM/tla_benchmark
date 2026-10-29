------------------------------ MODULE SpanTreeTest ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist, Edges

vars == <<mom, dist, Edges>>

(***************************************************************************)
(* The set of all valid undirected edge sets over Nodes: each edge is a    *)
(* two-element subset of Nodes.                                            *)
(***************************************************************************)
ValidEdgeSets ==
  {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ Edges \in ValidEdgeSets

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ Edges \in ValidEdgeSets

Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] + 1 < dist[n]
             /\ dist'  = [dist EXCEPT ![n] = dist[m] + 1]
             /\ mom'   = [mom  EXCEPT ![n] = m]
             /\ UNCHANGED Edges

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
-----------------------------------------------------------------------------
PostCondition ==
  \A n \in Nodes :
    \/ /\ n = Root
       /\ dist[n] = 0
       /\ mom[n] = n
    \/ /\ n # Root
       /\ dist[n] = MaxCardinality
       /\ mom[n] = n
       /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
    \/ /\ n # Root
       /\ dist[n] \in 1..(MaxCardinality - 1)
       /\ mom[n] \in Nbrs(n)
       /\ dist[n] = dist[mom[n]] + 1

Safety == []((~ ENABLED Next) => PostCondition)

Liveness == <>PostCondition

THEOREM Spec => []TypeOK /\ Safety /\ Liveness
=============================================================================