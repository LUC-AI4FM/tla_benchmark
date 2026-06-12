---- MODULE EchoProtocolInstantiation ----

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, InitNode, GraphFunc, ConnectedGraph

VARIABLES node, graph

Init == /\ node \in Nodes
        /\ graph = [n \in Nodes -> {m \in Nodes : <n, m> \in graph[node]}]

Next == \/ /\ node = InitNode
             /\ graph = GraphFunc
          \/ /\ node \in Nodes
             /\ graph = ConnectedGraph

Spec == Init /\ [][Next]_<<node, graph>>

CONSTRAINT NodeConstraint == InitNode \in Nodes

VARIABLE view

InitView == view = << >>

NextView == view' = <<view, node, graph>>

View == InitView /\ [][NextView]_<<view>>

PrintGraph == PRINT graph

TestSpec == Spec /\ View /\ PrintGraph

Postcondition == \A n \in Nodes : n \notin graph[n]

====