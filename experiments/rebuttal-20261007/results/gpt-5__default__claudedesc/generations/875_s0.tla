----------------------------- MODULE RandomizedSpanningTree -----------------------------

EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
  Nodes,
  Root,
  MaxCardinality

(*
  Assumptions about constants:
  - Root is a member of Nodes
  - MaxCardinality is a natural number and at least the number of nodes
  - We target randomized testing on a six-node graph
*)
ASSUME
  /\ Root \in Nodes
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes)
  /\ Cardinality(Nodes) = 6

(*
  Random undirected graph sampling:
  For each node u, RandAdj[u] is a random subset of Nodes \ {u}.
  The undirected edge set Edges includes {u,v} iff v \in RandAdj[u] or u \in RandAdj[v].
*)
RandAdj ==
  [u \in Nodes |-> RandomElement(SUBSET (Nodes \ {u}))]

Edges ==
  { {u, v} :
      u \in Nodes, v \in Nodes,
      u # v /\ (v \in RandAdj[u] \/ u \in RandAdj[v])
  }

Neighbors(n) ==
  { m \in Nodes : m # n /\ {n, m} \in Edges }

VARIABLES
  mom,   \* parent pointer of each node
  dist   \* distance estimate from Root

vars == << mom, dist >>

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E n \in Nodes :
    \E m \in Neighbors(n) :
      dist[m] + 1 < dist[n]
      /\ \E d \in (dist[m] + 1) .. (dist[n] - 1) :
           /\ mom' = [mom EXCEPT ![n] = m]
           /\ dist' = [dist EXCEPT ![n] = d]

(*
  PostCondition characterizes termination:
  - Root has distance 0
  - Every non-root node is either:
    - unreachable (distance = MaxCardinality) and all its neighbors are also unreachable, or
    - at distance exactly one greater than its parent's distance and the parent is a neighbor
*)
PostCondition ==
  /\ dist[Root] = 0
  /\ \A n \in Nodes :
       IF n = Root THEN TRUE
       ELSE
         ( (dist[n] = MaxCardinality
            /\ \A v \in Neighbors(n) : dist[v] = MaxCardinality)
         \/ (mom[n] \in Neighbors(n) /\ dist[n] = dist[mom[n]] + 1)
         )

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

(*
  Safety: whenever no further steps are enabled, the post-condition holds.
*)
Safety == []( ~ENABLED Next => PostCondition )

(*
  Liveness: the post-condition is eventually reached.
*)
Liveness == <>PostCondition

========================================================================================