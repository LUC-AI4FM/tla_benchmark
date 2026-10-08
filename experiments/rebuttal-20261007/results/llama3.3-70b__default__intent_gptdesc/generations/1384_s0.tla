```tla
MODULE GraphModel

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, FixedGraph, AuxiliaryGraph

VARIABLES Agent1Edge, Agent2Edge, AuxGraphForCheck

Init ==
  /\ Agent1Edge \in FixedGraph
  /\ Agent2Edge \in FixedGraph
  /\ AuxGraphForCheck = AuxiliaryGraph

Next ==
  /\ (Agent1Edge' \in FixedGraph)
  /\ (Agent2Edge' \in FixedGraph)
  /\ (AuxGraphForCheck' = AuxGraphForCheck)

Spec == Init /\ [][Next]_<<Agent1Edge, Agent2Edge, AuxGraphForCheck>>

THEOREM Spec => []<>(Agent1Edge \in FixedGraph)
THEOREM Spec => []<>(Agent2Edge \in FixedGraph)
THEOREM Spec => []<>(Agent1Edge \in AuxGraphForCheck)
THEOREM Spec => []<>(Agent2Edge \in AuxGraphForCheck)

THEOREM Spec => [](Len({x \in 1..5 : TRUE}) = 5)

Fairness == <<Agent1Edge, Agent2Edge>> 

INVARIANT Agent1Edge \in FixedGraph
INVARIANT Agent2Edge \in FixedGraph
INVARIANT Agent1Edge \in AuxGraphForCheck
INVARIANT Agent2Edge \in AuxGraphForCheck

=============================================================================
```