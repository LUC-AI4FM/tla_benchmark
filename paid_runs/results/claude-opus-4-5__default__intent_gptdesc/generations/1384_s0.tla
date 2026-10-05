-------------------------------- MODULE NondeterministicGraphAgents --------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Nodes,          \* Finite set of nodes
    FixedGraph,     \* The fixed directed graph (subset of Nodes × Nodes)
    AuxGraph        \* Auxiliary graph for cross-constraint checking

VARIABLES
    agent1Edge,     \* Edge currently held by agent 1
    agent2Edge      \* Edge currently held by agent 2

vars == <<agent1Edge, agent2Edge>>

-----------------------------------------------------------------------------
(* Type definitions and helpers *)

Edge == Nodes \X Nodes

TypeOK ==
    /\ agent1Edge \in Edge
    /\ agent2Edge \in Edge

(* The fixed graph must be a valid directed graph over Nodes *)
GraphOK == FixedGraph \subseteq Edge

(* The auxiliary graph must also be a valid directed graph over Nodes *)
AuxGraphOK == AuxGraph \subseteq Edge

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ FixedGraph # {}  \* Require non-empty fixed graph for agents to pick edges
    /\ agent1Edge \in FixedGraph
    /\ agent2Edge \in FixedGraph

-----------------------------------------------------------------------------
(* Transitions *)

(* Agent 1 nondeterministically selects any edge from the fixed graph *)
Agent1Step ==
    /\ agent1Edge' \in FixedGraph
    /\ UNCHANGED agent2Edge

(* Agent 2 nondeterministically selects any edge from the fixed graph *)
Agent2Step ==
    /\ agent2Edge' \in FixedGraph
    /\ UNCHANGED agent1Edge

(* Both agents may step simultaneously *)
BothStep ==
    /\ agent1Edge' \in FixedGraph
    /\ agent2Edge' \in FixedGraph

(* Next state: either agent steps, or both step *)
Next ==
    \/ Agent1Step
    \/ Agent2Step
    \/ BothStep

-----------------------------------------------------------------------------
(* Specification with fairness *)

Fairness ==
    /\ WF_vars(Agent1Step)
    /\ WF_vars(Agent2Step)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Safety: each agent's chosen edge is always a member of the fixed graph *)
SafetyInvariant ==
    /\ agent1Edge \in FixedGraph
    /\ agent2Edge \in FixedGraph

(* Cross-graph consistency: each agent's edge must also be in the auxiliary graph *)
(* This asserts a relationship between fixed and auxiliary graph edges *)
CrossGraphConsistency ==
    /\ agent1Edge \in AuxGraph
    /\ agent2Edge \in AuxGraph

(* Combined cross-graph constraint: if an edge is in FixedGraph and held by an agent,
   it must also be in AuxGraph. This implies FixedGraph ⊆ AuxGraph for reachable edges *)
CrossGraphRelationship ==
    /\ (agent1Edge \in FixedGraph) => (agent1Edge \in AuxGraph)
    /\ (agent2Edge \in FixedGraph) => (agent2Edge \in AuxGraph)

-----------------------------------------------------------------------------
(* Deterministic numeric assertion *)

(* Define a small finite set for bounded sequence computation *)
SmallSet == {1, 2, 3}

(* Bounded sequences of length up to 2 over SmallSet *)
BoundedSeqs == UNION {[1..n -> SmallSet] : n \in 0..2}

(* Compute a deterministic integer from bounded sequences *)
(* Count of all bounded sequences: empty seq (1) + length 1 (3) + length 2 (9) = 13 *)
ComputedValue == Cardinality(BoundedSeqs)

(* The expected constant value *)
ExpectedConstant == 13

(* Deterministic numeric assertion invariant *)
DeterministicNumericAssertion ==
    ComputedValue = ExpectedConstant

-----------------------------------------------------------------------------
(* Combined invariant for model checking *)

Invariant ==
    /\ TypeOK
    /\ SafetyInvariant
    /\ CrossGraphConsistency
    /\ DeterministicNumericAssertion

-----------------------------------------------------------------------------
(* Liveness property: agents can always eventually pick any edge in the fixed graph *)

Liveness ==
    /\ \A e \in FixedGraph : []<>(agent1Edge = e)
    /\ \A e \in FixedGraph : []<>(agent2Edge = e)

=============================================================================