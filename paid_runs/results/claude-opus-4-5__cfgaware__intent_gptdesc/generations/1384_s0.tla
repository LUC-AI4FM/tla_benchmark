---------------------------- MODULE specification ----------------------------

CONSTANTS Nodes

VARIABLES agent1Edge, agent2Edge, Graph, TestGraph

\* Define the set of all possible directed edges over Nodes
AllEdges == Nodes \X Nodes

\* Type invariant helper - checks if something is a valid edge set
IsEdgeSet(E) == E \subseteq AllEdges

\* Initial state predicate
Init ==
    /\ Graph \in SUBSET AllEdges           \* Graph is some arbitrary subset of all edges
    /\ Graph /= {}                          \* Graph must be non-empty for agents to pick edges
    /\ TestGraph \in SUBSET AllEdges       \* TestGraph is an arbitrary auxiliary graph
    /\ agent1Edge \in Graph                 \* Agent 1 starts with some edge from Graph
    /\ agent2Edge \in Graph                 \* Agent 2 starts with some edge from Graph

\* Agent 1 nondeterministically picks any edge from the fixed Graph
Agent1Step ==
    /\ agent1Edge' \in Graph
    /\ UNCHANGED <<agent2Edge, Graph, TestGraph>>

\* Agent 2 nondeterministically picks any edge from the fixed Graph
Agent2Step ==
    /\ agent2Edge' \in Graph
    /\ UNCHANGED <<agent1Edge, Graph, TestGraph>>

\* Next state relation - either agent can take a step
Next ==
    \/ Agent1Step
    \/ Agent2Step

\* Safety invariant: each agent's chosen edge is a member of the fixed graph
SafetyInvariant ==
    /\ agent1Edge \in Graph
    /\ agent2Edge \in Graph

\* Cross-graph consistency: each agent's edge must also be in the auxiliary TestGraph
\* This invariant will only hold when TestGraph is a superset of Graph
CrossGraphConsistency ==
    /\ agent1Edge \in TestGraph
    /\ agent2Edge \in TestGraph

\* Deterministic numeric assertion using bounded sequences over small finite sets
\* Compute the length of all sequences of length up to 2 over a set of 2 elements
SmallSet == {1, 2}
BoundedSeqs == UNION {[1..n -> SmallSet] : n \in 0..2}
\* The count is: 1 (empty) + 2 (length 1) + 4 (length 2) = 7
ComputedValue == Cardinality(BoundedSeqs)
ExpectedConstant == 7

DeterministicNumericAssertion ==
    ComputedValue = ExpectedConstant

\* Combined invariant for model checking
Inv ==
    /\ SafetyInvariant
    /\ CrossGraphConsistency
    /\ DeterministicNumericAssertion

\* Specification
Spec == Init /\ [][Next]_<<agent1Edge, agent2Edge, Graph, TestGraph>>

=============================================================================