---------------------------- MODULE GraphModel ----------------------------

CONSTANTS Nodes, Graph, TestGraph

VARIABLES agent1Edge, agent2Edge

Init == /\ agent1Edge \in Graph
        /\ agent2Edge \in Graph

Next == \/ /\ agent1Edge' \in Graph
               /\ agent2Edge' = agent2Edge
          \/ /\ agent1Edge' = agent1Edge
               /\ agent2Edge' \in Graph
          \/ /\ agent1Edge' \in Graph
               /\ agent2Edge' \in Graph

Inv == /\ agent1Edge \in Graph
       /\ agent2Edge \in Graph
       /\ agent1Edge \in TestGraph
       /\ agent2Edge \in TestGraph
       /\ StableAssertion

StableAssertion ==
    LET SmallSet == {1, 2, 3}
        SequenceLength == 5
        Expression == LAMBDA seq: \E i \in 1..SequenceLength : seq[i] = 2
    IN \A seq \in [1..SequenceLength -> SmallSet] : Expression[seq] = FALSE

=============================================================================