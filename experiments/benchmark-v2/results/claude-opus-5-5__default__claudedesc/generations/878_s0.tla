---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist
vars == <<mom, dist>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom  \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ \A n \in Nodes : dist[n] \in 0..MaxCardinality

Init == /\ mom  = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] + 1 < dist[n]
             /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
                   /\ dist' = [dist EXCEPT ![n] = d]
                   /\ mom'  = [mom  EXCEPT ![n] = m]

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

Safety == [](~ENABLED Next => PostCondition)

Liveness == <>(~ENABLED Next)

THEOREM Spec => []TypeOK /\ Safety /\ Liveness
-----------------------------------------------------------------------------
(* Model instantiation: five nodes, seven edges, connected, Root = n1.     *)
(* In the TLC configuration, override:                                       *)
(*   Nodes <- MCNodes, Edges <- MCEdges, Root <- MCRoot,                     *)
(*   MaxCardinality <- MCMaxCardinality                                      *)
MCNodes == {"n1", "n2", "n3", "n4", "n5"}

MCEdges == { {"n1", "n2"}, {"n1", "n3"}, {"n2", "n3"}, {"n2", "n4"},
             {"n3", "n4"}, {"n3", "n5"}, {"n4", "n5"} }

MCRoot == "n1"

MCMaxCardinality == 5
=============================================================================