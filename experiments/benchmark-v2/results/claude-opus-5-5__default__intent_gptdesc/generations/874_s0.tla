------------------------------ MODULE SelfStabilizingSpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,      \* finite set of nodes
          Edges,      \* finite set of undirected edges, each a 2-element set of nodes
          Root,       \* designated root node
          MaxDist,    \* maximum allowed distance label
          NoParent    \* model value: "no parent" marker for the root

VARIABLES parent,     \* parent[n] : chosen parent of n (NoParent for the root)
          dist        \* dist[n]   : distance estimate of n from the root

vars == <<parent, dist>>

-----------------------------------------------------------------------------------------------
(* Static graph definitions                                                                  *)
-----------------------------------------------------------------------------------------------

N == Cardinality(Nodes)

Nbrs(n) == { m \in Nodes : {n, m} \in Edges }

\* Within[k] = set of nodes within k hops of the root
Within[k \in 0..N] ==
    IF k = 0 THEN {Root}
    ELSE Within[k-1] \cup { n \in Nodes : Nbrs(n) \cap Within[k-1] # {} }

Connected == Within[N] = Nodes

\* True BFS (hop) distance from the root
BFS(n) == CHOOSE k \in 0..N : /\ n \in Within[k]
                              /\ (k = 0 \/ n \notin Within[k-1])

\* Eccentricity of the root (height of a BFS tree; bounded by the diameter)
Ecc == CHOOSE e \in { BFS(n) : n \in Nodes } :
           \A n \in Nodes : BFS(n) <= e

ASSUME /\ Root \in Nodes
       /\ NoParent \notin Nodes
       /\ Edges \subseteq { e \in SUBSET Nodes : Cardinality(e) = 2 }
       /\ Connected
       /\ MaxDist \in Nat
       /\ MaxDist >= Ecc

-----------------------------------------------------------------------------------------------
(* Helper operators over the current state                                                   *)
-----------------------------------------------------------------------------------------------

Min(S) == CHOOSE v \in S : \A w \in S : v <= w

MinNbrDist(n) == Min({ dist[q] : q \in Nbrs(n) })

\* Distance a non-root node should adopt, capped at MaxDist
NewDist(n) == IF MinNbrDist(n) + 1 > MaxDist THEN MaxDist ELSE MinNbrDist(n) + 1

\* Parent a non-root node should adopt (keep the current one if it is still a best choice)
NewParent(n) ==
    IF dist[parent[n]] = MinNbrDist(n)
    THEN parent[n]
    ELSE CHOOSE q \in Nbrs(n) : dist[q] = MinNbrDist(n)

\* Follow parent pointers k steps (stopping at the root)
RECURSIVE Up(_, _)
Up(n, k) == IF k = 0 \/ n = Root THEN n ELSE Up(parent[n], k - 1)

ReachesRoot(n) == \E k \in 0..N : Up(n, k) = Root

-----------------------------------------------------------------------------------------------
(* Initial states: arbitrary local states for non-root nodes;                                *)
(* the root holds no parent and distance 0 (its state is fixed).                             *)
-----------------------------------------------------------------------------------------------

Init ==
    /\ dist \in { d \in [Nodes -> 0..MaxDist] : d[Root] = 0 }
    /\ parent \in { p \in [Nodes -> Nodes \cup {NoParent}] :
                        /\ p[Root] = NoParent
                        /\ \A n \in Nodes \ {Root} : p[n] \in Nbrs(n) }

-----------------------------------------------------------------------------------------------
(* Actions                                                                                   *)
-----------------------------------------------------------------------------------------------

\* A non-root node reads its neighbors' distances and corrects its local state
\* if it is locally inconsistent.
Update(n) ==
    /\ n # Root
    /\ \/ dist[n] # NewDist(n)
       \/ parent[n] # NewParent(n)
    /\ dist'   = [dist   EXCEPT ![n] = NewDist(n)]
    /\ parent' = [parent EXCEPT ![n] = NewParent(n)]

-----------------------------------------------------------------------------------------------
(* Legitimate (stabilized) states                                                            *)
-----------------------------------------------------------------------------------------------

LocallyConsistent(n) ==
    n # Root => /\ dist[n] = NewDist(n)
                /\ parent[n] = NewParent(n)

Legit ==
    /\ dist[Root] = 0
    /\ parent[Root] = NoParent
    /\ \A n \in Nodes \ {Root} :
          /\ parent[n] \in Nbrs(n)
          /\ dist[n] = BFS(n)
          /\ dist[parent[n]] = dist[n] - 1

\* Stuttering once stabilized (avoids spurious deadlock reports)
Terminated == /\ \A n \in Nodes : LocallyConsistent(n)
              /\ UNCHANGED vars

Next == \/ \E n \in Nodes \ {Root} : Update(n)
        \/ Terminated

Fairness == \A n \in Nodes \ {Root} : WF_vars(Update(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------------
(* Safety properties                                                                         *)
-----------------------------------------------------------------------------------------------

TypeOK ==
    /\ dist \in [Nodes -> 0..MaxDist]
    /\ parent \in [Nodes -> Nodes \cup {NoParent}]

\* Every non-root node's parent is always a neighbor
ParentIsNeighbor == \A n \in Nodes \ {Root} : parent[n] \in Nbrs(n)

\* The root has no parent and distance zero
RootInvariant == parent[Root] = NoParent /\ dist[Root] = 0

\* Distance labels never exceed the specified maximum
DistBounded == \A n \in Nodes : dist[n] <= MaxDist

\* Parent pointers are acyclic: following them from every node reaches the root
NoCycles == \A n \in Nodes : ReachesRoot(n)

\* The parent relation forms a spanning tree rooted at Root
SpanningTree ==
    /\ RootInvariant
    /\ ParentIsNeighbor
    /\ NoCycles

\* Distances consistent with the parent relation
DistConsistent ==
    \A n \in Nodes \ {Root} : dist[n] = dist[parent[n]] + 1

\* In legitimate states the tree is a BFS spanning tree with correct distances,
\* and its height is bounded by the root's eccentricity (<= diameter) and MaxDist.
LegitIsCorrectTree ==
    Legit => /\ SpanningTree
             /\ DistConsistent
             /\ \A n \in Nodes : dist[n] <= Ecc
             /\ Ecc <= MaxDist
             /\ \A n \in Nodes : Up(n, Ecc) = Root

\* Legitimate states are fixed points: no node action is enabled
LegitIsQuiescent ==
    Legit => \A n \in Nodes : LocallyConsistent(n)

\* Once stable, distance labels and parents never change (in particular never decrease)
StableNonDecreasing ==
    [][Legit => /\ \A n \in Nodes : dist'[n] >= dist[n]
                /\ UNCHANGED vars]_vars

\* Closure: legitimacy is preserved
Closure == [](Legit => []Legit)

-----------------------------------------------------------------------------------------------
(* Liveness properties                                                                       *)
-----------------------------------------------------------------------------------------------

\* Convergence from arbitrary initial states to a BFS spanning tree
Stabilization == <>[]Legit

\* Eventually and permanently acyclic, connected spanning tree
EventuallyTree == <>[]SpanningTree

\* Eventually correct distances
EventuallyCorrectDist == <>[](\A n \in Nodes : dist[n] = BFS(n) /\ DistConsistent)

\* Termination: eventually no node action is enabled
EventuallyQuiescent == <>[](\A n \in Nodes : LocallyConsistent(n))

-----------------------------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ ParentIsNeighbor /\ RootInvariant /\ DistBounded
                   /\ LegitIsCorrectTree /\ LegitIsQuiescent)
THEOREM Spec => Closure /\ StableNonDecreasing
THEOREM Spec => Stabilization /\ EventuallyTree /\ EventuallyCorrectDist /\ EventuallyQuiescent
===============================================================================================