---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Integers, TLC

CONSTANT Nodes, Root
VARIABLE mom, dist

Edges == [n \in Nodes |-> RandomElement({m \in Nodes : m # n})]

TypeOK ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]
  /\ Root \in Nodes

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE 1]

Next(n) == 
  /\ n \in Nodes
  /\ \E m \in Nodes :
      /\ {m, n} \subseteq Edges[n]
      /\ dist[m] < dist[n]
      /\ mom' = [mom EXCEPT ![n] = m]
      /\ dist' = [dist EXCEPT ![n] = (dist[n] + dist[m]) \div 2]
  /\ UNCHANGED <<mom, dist>>

Spec == 
  /\ Init
  /\ [][Next(_)]_<<mom, dist>>
  /\ WF_vars(Next)

Safety == []TypeOK => [](Postcondition => Postcondition)
Liveness == <>Postcondition

Postcondition ==
  /\ \A n \in Nodes : mom[n] = n \/ {n, mom[n]} \subseteq Edges[n]
  /\ \A n \in Nodes : dist[n] = 0 <=> n = Root
  /\ \A n \in Nodes : mom[n] # n => dist[mom[n]] < dist[n]

=============================================================================