---- MODULE RandomSpanningTree ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
  Nodes,           \* finite set of nodes
  Root,            \* a distinguished root in Nodes
  MaxCardinality   \* an upper bound on graph diameter and "infinite" distance

ASSUME
  /\ Root \in Nodes
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes)

(*
  Random undirected graph generation:
  For each node n, pick a random subset Picks[n] of its potential neighbors Nodes \ {n}.
  The undirected edge set Edges contains an edge {n,m} if either endpoint picked the other.
*)
Picks ==
  [ n \in Nodes |-> RandomElement(SUBSET (Nodes \ {n})) ]

Edges ==
  { {n, m} : n \in Nodes, m \in Picks[n] }

Neighbors(n) ==
  { m \in Nodes : {n, m} \in Edges }

VARIABLES
  mom,   \* parent pointer: Nodes -> Nodes
  dist   \* distance estimate: Nodes -> 0..MaxCardinality

vars == << mom, dist >>

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
  /\ mom = [ n \in Nodes |-> n ]
  /\ dist = [ n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality ]

Next ==
  \E n \in Nodes:
    \E m \in Neighbors(n):
      /\ dist[m] < dist[n] - 1
      /\ \E d \in (dist[m] + 1)..(dist[n] - 1):
           /\ mom'  = [ mom  EXCEPT ![n] = m ]
           /\ dist' = [ dist EXCEPT ![n] = d ]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

PostCondition ==
  \A n \in Nodes:
    IF n = Root THEN
      dist[n] = 0
    ELSE
      IF dist[n] = MaxCardinality THEN
        \A m \in Neighbors(n): dist[m] = MaxCardinality
      ELSE
        dist[n] = dist[mom[n]] + 1

Safety ==
  []( ~ENABLED Next => PostCondition )

Liveness ==
  <>PostCondition

====