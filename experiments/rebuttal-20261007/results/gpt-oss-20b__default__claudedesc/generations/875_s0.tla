------------------------------ MODULE RandomSpanningTree ------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANTS Nodes, Root, MaxCardinality

Assumptions == Root \in Nodes
              /\ MaxCardinality \in Nat
              /\ MaxCardinality >= Cardinality(Nodes)

Edges == { <<Min(n,m), Max(n,m)>> : n \in Nodes /\ m \in RandomElement(Powerset(Nodes \ {n})) }

Adj == [n \in Nodes |-> {m \in Nodes : <<Min(n,m), Max(n,m)>> \in Edges}]

VARIABLES mom, dist

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes :> IF n = Root THEN 0 ELSE MaxCardinality]
  /\ Assumptions

Next ==
  \E n \in Nodes :
    \E m \in Adj[n] :
      (dist[m] < dist[n] - 1) /\
      \E newDist \in Nat :
        (dist[m]+1 <= newDist /\ newDist <= dist[n]-1) /\
        /\ mom