---------------------------- MODULE GraphModel ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes, Graph, TestGraph
VARIABLE agent1Edge, agent2Edge

Init ==
  /\ agent1Edge \in Graph
  /\ agent2Edge \in Graph

Next ==
  /\ agent1Edge' \in Graph
  /\ agent2Edge' \in Graph

Inv ==
  /\ agent1Edge \in Graph
  /\ agent2Edge \in Graph
  /\ agent1Edge \in TestGraph
  /\ agent2Edge \in TestGraph
  /\ (1 + 2) = 3

THEOREM Inv => [](Inv)
============================