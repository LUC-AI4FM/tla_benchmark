------------------------------ MODULE DistributedShortestPathTree ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,          \* finite set of graph nodes
          Edges,          \* set of undirected edges, each a 2-element subset of Nodes
          Root,           \* designated root node
          MaxCardinality  \* upper bound on distances (>= number of nodes)

VARIABLES dist,     \* dist[n]   : current best known distance of n from Root
          parent,   \* parent[n] : neighbor of n on current best path to Root
          msgs,     \* msgs[<<m,n>>] : queue of distance announcements from m to n
          started   \* TRUE once the root has initiated the algorithm

vars == <<dist, parent, msgs, started>>

-----------------------------------------------------------------------------------------------
\* Graph helpers

Neighbors(n) == { m \in Nodes : {m, n} \in Edges }

\* Directed channels: each undirected edge yields one queue in each direction
Channels == { c \in Nodes \X Nodes : {c[1], c[2]} \in Edges }

\* Set of nodes reachable from Root within k hops
RECURSIVE NodesWithin(_)
NodesWithin(k) ==
    IF k = 0 THEN {Root}
    ELSE NodesWithin(k - 1) \cup UNION { Neighbors(m) : m \in NodesWithin(k - 1) }

\* True shortest-path distance (in hops) from Root
ShortestDist(n) ==
    CHOOSE d \in 0..MaxCardinality :
        /\ n \in NodesWithin(d)
        /\ \A e \in 0..MaxCardinality : e < d => n \notin NodesWithin(e)

-----------------------------------------------------------------------------------------------
ASSUME
    /\ Root \in Nodes
    /\ IsFiniteSet(Nodes)
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2          \* undirected, no self-loops
    /\ MaxCardinality \in Nat
    /\ MaxCardinality >= Cardinality(Nodes)
    /\ NodesWithin(Cardinality(Nodes)) = Nodes       \* graph is connected

-----------------------------------------------------------------------------------------------
TypeOK ==
    /\ dist \in [Nodes -> 0..MaxCardinality]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs \in [Channels -> Seq(0..MaxCardinality)]
    /\ started \in BOOLEAN

Init ==
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs = [c \in Channels |-> << >>]
    /\ started = FALSE

\* The root initiates the algorithm by announcing distance 0 to all neighbors
RootStart ==
    /\ ~started
    /\ started' = TRUE
    /\ msgs' = [c \in Channels |->
                    IF c[1] = Root THEN Append(msgs[c], 0) ELSE msgs[c]]
    /\ UNCHANGED <<dist, parent>>

\* Node n picks any pending message (any order) from any incoming channel
Receive(n) ==
    /\ \E m \in Neighbors(n) :
         LET ch == <<m, n>> IN
         \E i \in 1..Len(msgs[ch]) :
            LET d    == msgs[ch][i]
                rest == SubSeq(msgs[ch], 1, i - 1) \o SubSeq(msgs[ch], i + 1, Len(msgs[ch]))
            IN
            IF d + 1 < dist[n]
            THEN /\ dist' = [dist EXCEPT ![n] = d + 1]
                 /\ parent' = [parent EXCEPT ![n] = m]
                 /\ msgs' = [c \in Channels |->
                                IF c = ch THEN rest
                                ELSE IF c[1] = n THEN Append(msgs[c], d + 1)
                                ELSE msgs[c]]
            ELSE /\ msgs' = [msgs EXCEPT ![ch] = rest]
                 /\ UNCHANGED <<dist, parent>>
    /\ UNCHANGED started

\* Stable state: algorithm started and all queues empty
Stable ==
    /\ started
    /\ \A c \in Channels : msgs[c] = << >>

\* Nodes keep running (checking for messages) after stabilization
Idle ==
    /\ Stable
    /\ UNCHANGED vars

Next ==
    \/ RootStart
    \/ \E n \in Nodes : Receive(n)
    \/ Idle

Fairness ==
    /\ WF_vars(RootStart)
    /\ \A n \in Nodes : WF_vars(Receive(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------------
\* Safety invariants

\* Computed distances never undercut the true distance
DistSound == \A n \in Nodes : dist[n] >= ShortestDist(n)

\* Any non-root node with a finite distance has a valid parent that is a neighbor
ParentConsistent ==
    \A n \in Nodes \ {Root} :
        dist[n] < MaxCardinality =>
            /\ parent[n] \in Neighbors(n)
            /\ dist[parent[n]] < dist[n]

\* Correctness of distances when stable
StableCorrectDist ==
    Stable => \A n \in Nodes : dist[n] = ShortestDist(n)

\* Valid spanning tree when stable: each non-root node's parent is a neighbor strictly closer
StableValidTree ==
    Stable =>
        /\ parent[Root] = Root
        /\ dist[Root] = 0
        /\ \A n \in Nodes \ {Root} :
              /\ parent[n] \in Neighbors(n)
              /\ dist[parent[n]] < dist[n]
              /\ dist[n] = dist[parent[n]] + 1

Invariants ==
    /\ TypeOK
    /\ DistSound
    /\ ParentConsistent
    /\ StableCorrectDist
    /\ StableValidTree

-----------------------------------------------------------------------------------------------
\* Temporal properties

\* Distances only improve (never increase)
DistMonotone == [][\A n \in Nodes : dist'[n] <= dist[n]]_vars

\* Once stable, the system remains stable with unchanged dist/parent
StableStays == [](Stable => [](Stable /\ UNCHANGED <<dist, parent>>))

\* Termination / stability: eventually stable forever
Termination == <>[]Stable

\* Eventual correctness of the result
EventuallyCorrect ==
    <>[](\A n \in Nodes : dist[n] = ShortestDist(n))

\* Progress: no node starves; every pending message channel is eventually drained
NoStarvation ==
    \A c \in Channels : (msgs[c] # << >>) ~> (msgs[c] = << >>)

\* Progress: the root eventually starts
EventuallyStarted == <>started

=============================================================================================