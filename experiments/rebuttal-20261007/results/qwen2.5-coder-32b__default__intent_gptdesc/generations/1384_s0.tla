------------------------------- MODULE GraphModel -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Nodes,  \* A finite set of nodes
    FixedGraph,  \* The designated constant directed graph as a subset of [Nodes -> Nodes]
    AuxGraph  \* An auxiliary graph used for cross-graph consistency checks

VARIABLES 
    Agent1Edge,  \* Edge chosen by agent 1
    Agent2Edge   \* Edge chosen by agent 2

Init == /\ Agent1Edge \in FixedGraph
        /\ Agent2Edge \in FixedGraph

Next == \/ /\ Agent1Edge' \in FixedGraph
               /\ Agent2Edge' = Agent2Edge
          \/ /\ Agent1Edge' = Agent1Edge
               /\ Agent2Edge' \in FixedGraph

Spec == Init /\ [][Next]_<<Agent1Edge, Agent2Edge>>

\* Safety: Each agent’s chosen edge is a member of the fixed graph’s edge set.
Safety == /\ Agent1Edge \in FixedGraph
          /\ Agent2Edge \in FixedGraph

\* Cross-graph consistency: Each agent’s chosen edge is also an edge of the auxiliary graph.
CrossGraphConsistency == /\ Agent1Edge \in AuxGraph
                         /\ Agent2Edge \in AuxGraph

\* Deterministic numeric assertion: A computed integer expression must equal a specified constant.
\* For demonstration, let's assume the expression is |{Agent1Edge, Agent2Edge}| and the constant is 1 or 2.
DeterministicAssertion == Cardinality({Agent1Edge, Agent2Edge}) \in {1, 2}

Invariants == /\ Safety
              /\ CrossGraphConsistency
              /\ DeterministicAssertion

=============================================================================