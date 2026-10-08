---- MODULE SpanningTree ----
EXTENDS Naturals, FiniteSets

(*
  Constants:
    - Nodes: a finite set of nodes
    - Edges: a set of 2-element subsets of Nodes (undirected edges)
    - Root:  the designated root node in Nodes
    - MaxCardinality: a natural bound >= Cardinality(Nodes)
*)
CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Root \in Nodes
  /\ MaxCardinality \in Nat
  /\ Cardinality(Nodes) <= MaxCardinality
  /\ \A e \in Edges: e \subseteq Nodes /\ Cardinality(e) = 2

VARIABLES mom, dist

vars == << mom, dist >>

Neighbors(n) == { m \in Nodes: m # n /\ {m, n} \in Edges }

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Improvement(n, m) ==
  /\ m \in Neighbors(n)
  /\ dist[m] + 1 < dist[n]

Next ==
  \E n \in Nodes:
    \E m \in Neighbors(n):
      /\ Improvement(n, m)
      /\ \E d \in 0..MaxCardinality:
           /\ dist[m] + 1 <= d
           /\ d < dist[n]
           /\ mom'  = [mom EXCEPT ![n] = m]
           /\ dist' = [dist EXCEPT ![n] = d]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Terminated == ~ENABLED Next

Post ==
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A n \in Nodes:
       IF n = Root THEN TRUE
       ELSE
         IF dist[n] = MaxCardinality
         THEN
           /\ mom[n] = n
           /\ \A m \in Neighbors(n): dist[m] = MaxCardinality
         ELSE
           /\ mom[n] \in Neighbors(n)
           /\ dist[n] = dist[mom[n]] + 1

Safety == [] (~ENABLED Next => Post)

Liveness == <> Terminated

====