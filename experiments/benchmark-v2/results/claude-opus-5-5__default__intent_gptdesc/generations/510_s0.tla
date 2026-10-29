------------------------------ MODULE DistributedBFS ------------------------------
(***************************************************************************)
(* Asynchronous distributed shortest-path (hop-count) tree construction.   *)
(* Every node learns its hop distance to Root and picks a parent that lies *)
(* on a shortest path to Root. Channels are reliable FIFO queues, one per  *)
(* ordered neighbor pair.                                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,            \* finite set of nodes
    Edges,            \* set of undirected edges, each a 2-element set {a, b}
    Root,             \* the designated root node
    NoParent,         \* model value: "no parent recorded"
    SuppressToSender  \* BOOLEAN: optional optimization, skip echo to the supplier

ASSUME RootInNodes   == Root \in Nodes
ASSUME FiniteNodes   == IsFiniteSet(Nodes)
ASSUME EdgesWellFormed ==
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2
ASSUME NoParentFresh == NoParent \notin Nodes
ASSUME SuppressBool  == SuppressToSender \in BOOLEAN

N == Cardinality(Nodes)

\* Sentinel "unknown" distance: strictly larger than any real hop distance.
Infinity == N

Nbrs(n) == { m \in Nodes : {n, m} \in Edges }

\* Ordered neighbor pairs <<sender, receiver>>; one FIFO channel per pair.
Channels == { <<m, n>> \in Nodes \X Nodes : {m, n} \in Edges }

\* Within[k] = set of nodes at hop distance <= k from Root.
Within[k \in 0..N] ==
    IF k = 0 THEN {Root}
    ELSE Within[k-1] \cup { m \in Nodes : \E x \in Within[k-1] : m \in Nbrs(x) }

ASSUME Connected == Within[N] = Nodes

\* Graph-theoretic shortest-path distance to Root.
SPDist(n) == CHOOSE k \in 0..N : /\ n \in Within[k]
                                 /\ (k = 0 \/ n \notin Within[k-1])

VARIABLES
    dist,     \* dist[n]   : current distance estimate of node n
    parent,   \* parent[n] : current parent of node n
    queue     \* queue[c]  : FIFO sequence of distances in transit on channel c

vars == << dist, parent, queue >>

---------------------------------------------------------------------------------

TypeOK ==
    /\ dist   \in [Nodes -> 0..Infinity]
    /\ parent \in [Nodes -> Nodes \cup {NoParent}]
    /\ queue  \in [Channels -> Seq(0..Infinity)]

Init ==
    /\ dist   = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
    /\ parent = [n \in Nodes |-> NoParent]
    \* The root starts the computation by having announced distance 0.
    /\ queue  = [c \in Channels |-> IF c[1] = Root THEN <<0>> ELSE << >>]

\* Neighbors to which n forwards its new distance after learning it from m.
Targets(n, m) == IF SuppressToSender THEN Nbrs(n) \ {m} ELSE Nbrs(n)

\* Node n receives and processes the head message on channel <<m, n>>.
Receive(m, n) ==
    /\ <<m, n>> \in Channels
    /\ queue[<<m, n>>] # << >>
    /\ LET d == Head(queue[<<m, n>>]) IN
         IF d + 1 < dist[n]
         THEN \* Strict improvement: adopt it, record parent, and propagate.
              /\ dist'   = [dist   EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ queue'  = [c \in Channels |->
                              IF c = <<m, n>> THEN Tail(queue[c])
                              ELSE IF c[1] = n /\ c[2] \in Targets(n, m)
                                   THEN Append(queue[c], d + 1)
                                   ELSE queue[c]]
         ELSE \* No improvement: discard the message.
              /\ queue'  = [queue EXCEPT ![<<m, n>>] = Tail(@)]
              /\ UNCHANGED << dist, parent >>

\* All channels empty: the algorithm has quiesced (stutter to avoid deadlock).
Quiescent == \A c \in Channels : queue[c] = << >>

Terminated == Quiescent /\ UNCHANGED vars

Next ==
    \/ \E c \in Channels : Receive(c[1], c[2])
    \/ Terminated

Fairness == \A c \in Channels : WF_vars(Receive(c[1], c[2]))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------
(* Safety invariants *)

\* Estimates are never below the true distance.
DistanceSound == \A n \in Nodes : dist[n] >= SPDist(n)

\* The root never changes.
RootStable == dist[Root] = 0 /\ parent[Root] = NoParent

\* Every non-root node with a known distance has a neighbor parent whose
\* distance is at most one less (equal to dist - 1 once converged).
ParentValidity ==
    \A n \in Nodes \ {Root} :
        dist[n] < Infinity =>
            /\ parent[n] \in Nbrs(n)
            /\ dist[parent[n]] + 1 <= dist[n]

\* Unknown distance iff no parent (for non-root nodes).
ParentIffKnown ==
    \A n \in Nodes \ {Root} : (parent[n] = NoParent) <=> (dist[n] = Infinity)

\* Messages in transit never carry a value smaller than the sender's true distance.
MessagesSound ==
    \A c \in Channels : \A i \in 1..Len(queue[c]) : queue[c][i] >= SPDist(c[1])

Converged == \A n \in Nodes : dist[n] = SPDist(n)

\* Parent lies on a shortest path: parent is a neighbor with distance dist - 1.
ParentOnShortestPath ==
    \A n \in Nodes \ {Root} :
        /\ parent[n] \in Nbrs(n)
        /\ dist[parent[n]] = dist[n] - 1

\* When the system is quiescent, the result is correct.
QuiescentCorrect == Quiescent => (Converged /\ ParentOnShortestPath)

Invariants ==
    /\ TypeOK
    /\ DistanceSound
    /\ RootStable
    /\ ParentValidity
    /\ ParentIffKnown
    /\ MessagesSound
    /\ QuiescentCorrect

---------------------------------------------------------------------------------
(* Temporal properties *)

\* Distances are monotonically non-increasing.
DistMonotone == [][\A n \in Nodes : dist'[n] <= dist[n]]_vars

\* Once a node's distance reaches its final value, it never changes again.
FinalDistanceStable ==
    \A n \in Nodes : [](dist[n] = SPDist(n) => [](dist[n] = SPDist(n)))

\* Convergence: eventually every node permanently knows its true distance.
Convergence == <>[]Converged

\* Eventually every non-root node permanently has a valid shortest-path parent.
ParentConvergence == <>[]ParentOnShortestPath

\* All messages are eventually consumed.
Termination == <>[]Quiescent

THEOREM Spec => []Invariants
THEOREM Spec => DistMonotone /\ FinalDistanceStable
THEOREM Spec => Convergence /\ ParentConvergence /\ Termination
=================================================================================