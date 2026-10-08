--------------------------- MODULE ShortestPathTree ---------------------------

EXTENDS Naturals, Sequences

CONSTANTS 
  Nodes, \* Nonempty set of nodes
  Root,  \* Distinguished root node
  E,     \* Set of directed edges with symmetry (undirected graph)
  Inf    \* A special value representing infinity (not in Nat)

(*
  Graph assumptions: undirected and connected to Root.
  The graph is nondeterministically chosen via constants and is thereafter static.
*)
ASSUME
  /\ Nodes # {}
  /\ Root \in Nodes
  /\ E \subseteq Nodes \X Nodes
  /\ \A u \in Nodes: \A v \in Nodes: (<<u,v>> \in E) <=> (<<v,u>> \in E)
  /\ Inf \notin Nat
  /\ \A n \in Nodes:
       \E s \in Seq(Nodes):
         /\ Len(s) >= 1
         /\ s[1] = Root
         /\ s[Len(s)] = n
         /\ \A i \in 1..(Len(s)-1): <<s[i], s[i+1]>> \in E

VARIABLES parent, dist

vars == << parent, dist >>

(*
  Basic operators on distances (Nat union {Inf})
*)
DistDomain == Nat \cup {Inf}
Finite(d) == d \in Nat
Plus1(d) == IF Finite(d) THEN d + 1 ELSE Inf

(*
  Ordering that treats any finite number as less than Inf.
*)
Less(d1, d2) ==
  (d2 = Inf /\ Finite(d1))
  \/ (Finite(d1) /\ Finite(d2) /\ d1 < d2)

Adj(u, v) == <<u, v>> \in E
Neighbors(n) == { v \in Nodes : Adj(n, v) }

(*
  Initialization: each node is its own parent; root has distance 0, others Inf.
*)
Init ==
  /\ parent \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistDomain]
  /\ parent = [n \in Nodes |-> n]
  /\ dist   = [n \in Nodes |-> IF n = Root THEN 0 ELSE Inf]

(*
  A node n (non-root) can adopt a neighbor p with strictly smaller distance,
  and set its distance to one more than p's distance (never increasing).
  Parent and distance are updated atomically to preserve safety invariants.
*)
Update(n) ==
  \E p \in Nodes:
    /\ n \in Nodes \ {Root}
    /\ Adj(n, p)
    /\ Less(dist[p], dist[n])
    /\ parent' = [parent EXCEPT ![n] = p]
    /\ dist'   = [dist   EXCEPT ![n] = Plus1(dist[p])]

(*
  Allow stuttering to model asynchrony; fairness will prevent starvation.
*)
Next ==
  \/ \E n \in Nodes \ {Root}: Update(n)
  \/ UNCHANGED vars

(*
  Fairness: if an Update(n) stays enabled, it will eventually occur (no starvation).
*)
Fairness == \A n \in Nodes \ {Root}: WF_vars(Update(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety invariants
*)
TypeOK ==
  /\ parent \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistDomain]

ParentOK ==
  \A n \in Nodes: parent[n] = n \/ Adj(n, parent[n])

DistOK ==
  \A n \in Nodes: dist[n] \in DistDomain

RootOK ==
  /\ dist[Root] = 0
  /\ parent[Root] = Root

FiniteZeroIsRoot ==
  \A n \in Nodes: dist[n] = 0 => n = Root

ConsistencyOK ==
  \A n \in Nodes:
    IF n = Root THEN
      /\ dist[n] = 0
      /\ parent[n] = Root
    ELSE IF dist[n] = Inf THEN
      /\ parent[n] = n
    ELSE
      /\ Finite(dist[n])
      /\ dist[n] = Plus1(dist[parent[n]])
      /\ parent[n] # n
      /\ Adj(n, parent[n])

Safety == TypeOK /\ ParentOK /\ DistOK /\ RootOK /\ FiniteZeroIsRoot /\ ConsistencyOK

(*
  Enabledness for stability/postcondition
*)
EnabledUpdate(n) ==
  /\ n \in Nodes \ {Root}
  /\ \E p \in Nodes: Adj(n,p) /\ Less(dist[p], dist[n])

Stable ==
  \A n \in Nodes \ {Root}: ~EnabledUpdate(n)

(*
  Postcondition at convergence: each node is either
  - the root; or
  - unreached (Inf, self-parent, and all neighbors also Inf); or
  - reached with finite distance equal to parent-distance+1 and parent is a neighbor.
*)
Post ==
  \A n \in Nodes:
    \/ n = Root
    \/ (/\ dist[n] = Inf
        /\ parent[n] = n
        /\ \A p \in Neighbors(n): dist[p] = Inf)
    \/ (/\ Finite(dist[n])
        /\ parent[n] \in Nodes
        /\ Adj(n, parent[n])
        /\ dist[n] = Plus1(dist[parent[n]]))

(*
  Convergence (liveness): eventually a stable global state satisfying Post is reached.
*)
Convergence == []<>(Stable /\ Post)

=============================================================================