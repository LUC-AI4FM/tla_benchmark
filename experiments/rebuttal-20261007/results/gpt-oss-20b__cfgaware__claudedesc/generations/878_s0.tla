------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

(* Assumptions about constants *)
Assume ==
  /\ Root \in Nodes
  /\ Edges \subseteq { e \in SUBSET Nodes : #e = 2 }
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= #Nodes

VARIABLES mom, dist

Neighbors(n) == { m \in Nodes : {n, m} \in Edges }

Init ==
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
  /\ mom = [n \in Nodes |-> n]

Next ==
  \E n \in Nodes :
    \E m \in Neighbors(n) :
      /\ dist[m] + 1 < dist[n]
      /\ LET d == CHOOSE d' \in Nat : dist[m] + 1 <= d' /\ d' < dist[n] IN
         /\ dist' = [dist EXCEPT ![n] = d]
         /\ mom' = [mom EXCEPT ![n] = m]

Spec ==
  Init /\ [][Next]_<<mom, dist>> /\ WF_<<mom, dist>>(Next) /\ Assume

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]
  /\ \A n \in Nodes : dist[n] <= MaxCardinality

Post ==
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A n \in Nodes :
        IF dist[n] = MaxCardinality THEN
           /\ mom[n] = n
           /\ \A m \in Neighbors(n) : dist[m] = MaxCardinality
        ELSE
           /\ mom[n] \in Neighbors(n)
           /\ dist[n] = dist[mom[n]] + 1

NextDisabled ==
  \A n \in Nodes :
    \A m \in Neighbors(n) : NOT (dist[m] + 1 < dist[n])

Safety ==
  TypeOK /\ NextDisabled => Post

Liveness ==
  <> NextDisabled
=============================================================================