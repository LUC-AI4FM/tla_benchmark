------------------------------ MODULE SpanningTree ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Nodes,        \* finite set of nodes
  Edges,        \* set of undirected edges, each a 2-element subset of Nodes
  Root,         \* distinguished root node in Nodes
  UpperBound    \* natural upper bound (at least the number of nodes)

VARIABLES
  Dist,         \* function Nodes -> 0..UpperBound
  Parent,       \* function Nodes -> Nodes
  Done          \* boolean flag indicating termination

vars == << Dist, Parent, Done >>

\* Undirected adjacency
IsEdge(x, y) == /\ x \in Nodes /\ y \in Nodes
                /\ x # y
                /\ {x, y} \in Edges

Neighbors(n) == { m \in Nodes : IsEdge(n, m) }

GraphWellFormed ==
  /\ IsFiniteSet(Nodes)
  /\ Root \in Nodes
  /\ UpperBound \in Nat
  /\ UpperBound >= Cardinality(Nodes)
  /\ Edges \subseteq { e \in SUBSET Nodes : Cardinality(e) = 2 }

Init ==
  /\ GraphWellFormed
  /\ Dist = [ n \in Nodes |-> IF n = Root THEN 0 ELSE UpperBound ]
  /\ Parent = [ n \in Nodes |-> n ]
  /\ Done = FALSE

CanImprove ==
  \E n \in Nodes:
  \E m \in Nodes:
    /\ IsEdge(n, m)
    /\ Dist[n] > Dist[m] + 1

\* One local improvement: pick a node n, a neighbor m with smaller distance,
\* and lower n's distance to any integer in [Dist[m]+1, Dist[n)-1], setting m as parent.
Improve ==
  \E n \in Nodes:
  \E m \in Nodes:
  \E d \in (Dist[m] + 1) .. (Dist[n] - 1):
    /\ IsEdge(n, m)
    /\ Dist[n] > Dist[m] + 1
    /\ Dist' = [Dist EXCEPT ![n] = d]
    /\ Parent' = [Parent EXCEPT ![n] = m]
    /\ Done' = Done

\* Declare termination when no improvement is possible.
Terminate ==
  /\ ~CanImprove
  /\ Done = FALSE
  /\ UNCHANGED << Dist, Parent >>
  /\ Done' = TRUE

Next == Improve \/ Terminate

Terminated == Done \/ ~CanImprove

\* Reachability from Root via undirected edges
IsPath(s) ==
  /\ s \in Seq(Nodes)
  /\ Len(s) >= 1
  /\ \A i \in 1..(Len(s)-1): IsEdge(s[i], s[i+1])

Reachable(n) ==
  \E s \in Seq(Nodes):
    /\ Len(s) >= 1
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1..(Len(s)-1): IsEdge(s[i], s[i+1])

\* Safety condition describing the final spanning-tree structure
TreeOK ==
  /\ Dist[Root] = 0
  /\ Parent[Root] = Root
  /\ \A n \in Nodes \ {Root}:
       IF Reachable(n)
       THEN /\ Dist[n] < UpperBound
            /\ IsEdge(n, Parent[n])
            /\ Dist[n] = Dist[Parent[n]] + 1
       ELSE /\ Dist[n] = UpperBound
            /\ Parent[n] = n
            /\ \A m \in Neighbors(n): Dist[m] >= Dist[n]

TypeOK ==
  /\ GraphWellFormed
  /\ Dist \in [Nodes -> 0..UpperBound]
  /\ Parent \in [Nodes -> Nodes]
  /\ Done \in BOOLEAN

Safety == [](Terminated => TreeOK)

Liveness == <>Terminated

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Improve)

=============================================================================