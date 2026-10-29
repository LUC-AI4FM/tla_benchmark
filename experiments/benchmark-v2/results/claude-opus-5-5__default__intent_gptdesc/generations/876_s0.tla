--------------------------- MODULE BFSSpanningTree ---------------------------
(***************************************************************************)
(* Distributed breadth-first spanning-tree construction on an undirected   *)
(* graph.  The set of nodes is fixed, but the set of edges is initially     *)
(* unknown: it may be any set of undirected links between distinct nodes.  *)
(* Each node keeps a distance-to-root estimate and a parent pointer.       *)
(* A node with no parent points to itself.  In one atomic, asynchronous    *)
(* step, a non-root node reads a neighbor's current distance.  If that      *)
(* distance plus one is smaller than its own estimate, the node adopts the  *)
(* neighbor as its parent and updates its distance.  The root always       *)
(* advertises distance 0 and never changes its parent.  Unreachable nodes   *)
(* keep distance Infinity and no parent.                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,          \* the fixed set of nodes
          Root,           \* the distinguished root node
          MaxCardinality  \* bound used as the "infinite" distance

ASSUME RootAssump == Root \in Nodes
ASSUME FiniteNodes == IsFiniteSet(Nodes)
ASSUME MaxCardAssump ==
          /\ MaxCardinality \in Nat
          /\ MaxCardinality >= Cardinality(Nodes)

(***************************************************************************)
(* Infinity is larger than any possible shortest-path length, because a    *)
(* shortest path has at most Cardinality(Nodes) - 1 edges.                 *)
(***************************************************************************)
Infinity == MaxCardinality

Dist == 0..Infinity

(* All possible undirected links between distinct nodes *)
Edges == { {m, n} : m, n \in Nodes } \ { {n} : n \in Nodes }

VARIABLES nbrs,   \* the (initially unknown, then fixed) set of undirected edges
          mom,    \* mom[n] : parent of n (n itself means "no parent")
          dist    \* dist[n] : current distance-to-root estimate of n

vars == << nbrs, mom, dist >>

Nbrs(n) == { m \in Nodes : {m, n} \in nbrs }

(***************************************************************************)
(* Graph-theoretic definitions used to state correctness.                  *)
(* R[k] is the set of nodes whose distance from Root is at most k.         *)
(***************************************************************************)
R[k \in 0..MaxCardinality] ==
    IF k = 0 THEN {Root}
             ELSE R[k-1] \cup { n \in Nodes : \E m \in R[k-1] : {m, n} \in nbrs }

ReachableFromRoot == R[MaxCardinality]

ShortestDist(n) ==
    CHOOSE k \in 0..MaxCardinality :
        /\ n \in R[k]
        /\ (k = 0 \/ n \notin R[k-1])

-----------------------------------------------------------------------------
TypeOK ==
    /\ nbrs \subseteq Edges
    /\ \A e \in nbrs : Cardinality(e) = 2          \* undirected, distinct endpoints
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Dist]

Init ==
    /\ nbrs \in SUBSET Edges                       \* arbitrary undirected topology
    /\ mom  = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

(* Node n adopts neighbor m as its parent, based only on m's current distance *)
Update(n, m) ==
    /\ n # Root
    /\ m \in Nbrs(n)
    /\ dist[m] < Infinity
    /\ dist[m] + 1 < dist[n]
    /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
    /\ mom'  = [mom  EXCEPT ![n] = m]
    /\ UNCHANGED nbrs

Next == \E n \in Nodes : \E m \in Nodes : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Structural invariants                                                   *)
(***************************************************************************)
RootInv ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root

NoParentInv ==
    \A n \in Nodes : (dist[n] = Infinity) <=> (mom[n] = n /\ n # Root)

ParentInv ==
    \A n \in Nodes \ {Root} :
        dist[n] < Infinity =>
            /\ mom[n] \in Nbrs(n)
            /\ dist[mom[n]] < dist[n]

(* Estimates never undershoot the true shortest distance *)
LowerBoundInv ==
    \A n \in Nodes :
        dist[n] < Infinity => (n \in ReachableFromRoot /\ ShortestDist(n) <= dist[n])

(***************************************************************************)
(* Postcondition: the parent pointers form a shortest-path (BFS) tree.     *)
(***************************************************************************)
PostCondition ==
    \A n \in Nodes :
        \/ /\ n = Root
           /\ dist[n] = 0
           /\ mom[n] = n
        \/ /\ n # Root
           /\ n \notin ReachableFromRoot
           /\ dist[n] = Infinity
           /\ mom[n] = n
           /\ \A m \in Nbrs(n) : dist[m] = Infinity
        \/ /\ n # Root
           /\ n \in ReachableFromRoot
           /\ mom[n] \in Nbrs(n)
           /\ dist[n] = ShortestDist(n)
           /\ dist[mom[n]] = dist[n] - 1

Terminated == ~ ENABLED Next

(* Safety: whenever no further action is enabled, the postcondition holds *)
Safety == Terminated => PostCondition

(* Liveness: under fair scheduling a stable correct configuration is reached *)
Liveness == <>[] PostCondition

TerminationLiveness == <> Terminated

THEOREM Spec => [](TypeOK /\ RootInv /\ NoParentInv /\ ParentInv /\ LowerBoundInv /\ Safety)
THEOREM Spec => Liveness /\ TerminationLiveness
=============================================================================