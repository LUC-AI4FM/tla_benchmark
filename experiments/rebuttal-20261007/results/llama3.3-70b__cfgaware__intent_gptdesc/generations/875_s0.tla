---------------------------- MODULE ShortestPathTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes, Root
VARIABLE parent, distance

TypeOK == 
  /\ parent \in [Nodes -> Nodes]
  /\ distance \in [Nodes -> (Nat \cup {<<"inf">>})]

Init ==
  /\ TypeOK
  /\ parent = [n \in Nodes |-> IF n = Root THEN n ELSE n]
  /\ distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE <<"inf">>]

Next(n \in Nodes) == 
  /\ parent' = [parent EXCEPT ![n] = some neighbor \in {m \in Nodes : {n, m} \subseteq unreachablyConnected(Nodes, parent)}
                                            /\ distance[neighbor] < distance[n]]
  /\ distance' = [distance EXCEPT ![n] = IF distance'[n] = <<"inf">> THEN <<"inf">>
                                                  ELSE 1 + distance[neighbor]]

unreachablyConnected(nodes, parent) == 
  LET reachable == {n \in nodes : distance[n] # <<"inf">>}
  IN {n, m} : n \in nodes /\ m \in nodes /\ (n = m \/ <<n, m>> \subseteq reachable)

Spec == Init /\ [][Next(VARIABLES)]

Safety == 
  /\ TypeOK
  /\ parent \in [Nodes -> Nodes]
  /\ distance \in [Nodes -> (Nat \cup {<<"inf">>})]
  /\ \A n \in Nodes : IF distance[n] # <<"inf">> THEN distance[n] = 1 + distance[parent[n]]
  /\ Root \in Nodes
  /\ parent[Root] = Root
  /\ distance[Root] = 0

Liveness == <>[]<<Safety /\ \A n \in Nodes : 
                        (n = Root \/ distance[n] = <<"inf">> 
                         \/ (distance[n] # <<"inf">> /\ distance[n] = 1 + distance[parent[n]]))>> 

THEOREM Spec => []Safety
THEOREM Spec => Liveness

===============================================================================