------------------------------ MODULE RootedSpanningTree ------------------------------
EXTENDS Naturals

CONSTANTS
    Nodes,            \* Set of node identifiers
    Adj,              \* Undirected adjacency relation: [Nodes -> SUBSET Nodes]
    Root,             \* Distinguished root node (Root ∈ Nodes)
    MaxCardinality    \* Finite stand‑in for infinity (a natural number)

ASSUME
    /\ Root ∈ Nodes
    /\ Adj ⊆ [Nodes -> SUBSET Nodes]
    /\ ∀i ∈ Nodes : i ∈ Adj[i]      \* Each node is adjacent to itself
    /\ ∀i, j ∈ Nodes :
           (j ∈ Adj[i]) ⇒ (i ∈ Adj[j])

VARIABLES mom, dist

(* ---------------------------------------------------------------------- *)
(*  State Invariants                                                     *)

NoCycles ==
    ∀i ∈ Nodes : (i = Root) \/ (mom[i] ≠ i)

AdjacencyInvariant ==
    ∀i ∈ Nodes :
        IF i = Root THEN mom[i] = Root
        ELSE mom[i] ∈ Adj[i]

DistanceInvariant ==
    ∀i ∈ Nodes :
        IF i = Root THEN dist[i] = 0
        ELSE dist[i] > 0 /\ dist[mom[i]] < dist[i]

SafetyInvariant == NoCycles /\ AdjacencyInvariant /\ DistanceInvariant

(* ---------------------------------------------------------------------- *)
(*  Postcondition when the algorithm has stopped                         *)

Stopped ==
    ¬∃i ∈ Nodes, j ∈ Adj[i] : dist[j] < dist[i]

Postcondition ==
    ∀i ∈ Nodes :
        IF i = Root THEN
            mom[i] = Root /\ dist[i] = 0
        ELSE
            mom[i] ≠ i /\ mom[i] ∈ Adj[i] /\ dist[i] = dist[mom[i]] + 1

PostconditionWhenStopped == Stopped => Postcondition

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                        *)

Init ==
    /\ mom = [i \in Nodes |-> i]
    /\ dist = [i \in Nodes |
                IF i = Root THEN 0
                ELSE MaxCardinality]

(* ---------------------------------------------------------------------- *)
(*  One step of the algorithm                                            *)

Next ==
    ∃i ∈ Nodes, j ∈ Adj[i], newDist ∈ Nat :
        /\ j ∈ Adj[i]
        /\ dist[j] < dist[i]
        /\ newDist >= dist[j] + 1
        /\ newDist < dist[i]
        /\ mom' = [mom EXCEPT ![i] = j]
        /\ dist' = [dist EXCEPT ![i] = newDist]

(* ---------------------------------------------------------------------- *)
(*  Temporal specification                                                *)

Spec ==
    Init
    /\ [][Next]_<<mom, dist>>
    /\ WF_1(Next)
    /\ SafetyInvariant
    /\ PostconditionWhenStopped
    /\ ◇ Stopped
    /\ ∀i ∈ Nodes : ◇ (mom[i] = Root)

=============================================================================