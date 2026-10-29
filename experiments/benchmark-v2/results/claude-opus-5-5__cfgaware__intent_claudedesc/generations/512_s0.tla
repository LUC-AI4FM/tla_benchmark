------------------------------ MODULE ShortestPathTree ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,      \* set of nodes of the graph
    Edges,      \* set of undirected edges, each a 2-element set {a, b}
    root,       \* distinguished root node
    MaxNodes    \* upper bound on the number of nodes; also serves as "infinity"

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat /\ MaxNodes >= Cardinality(Nodes)
ASSUME \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

VARIABLES
    depth,      \* depth[n] : current known distance of n from root
    parent,     \* parent[n] : neighbor through which n reaches root
    msgs        \* msgs[<<from, to>>] : FIFO channel of distance announcements

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
(* Graph helpers *)

SetNbrs(n) == { m \in Nodes : {m, n} \in Edges }

\* Each undirected link is modeled as a pair of directed FIFO queues.
Queues == { <<a, b>> \in Nodes \X Nodes : {a, b} \in Edges }

Infinity == MaxNodes

\* Set of nodes reachable from root within k hops
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {root}
            ELSE Reach(k-1) \cup UNION { SetNbrs(m) : m \in Reach(k-1) }

\* True shortest-path distance from root
Dist(n) == CHOOSE k \in 0..MaxNodes :
               /\ n \in Reach(k)
               /\ \A j \in 0..MaxNodes : j < k => n \notin Reach(j)

-----------------------------------------------------------------------------
TypeOK ==
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs \in [Queues -> Seq(0..MaxNodes)]

Init ==
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE Infinity]
    /\ parent = [n \in Nodes |-> n]
    \* The root initiates by announcing distance 0 to all its neighbors
    /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE << >>]

\* Node n receives an announcement from neighbor m
Receive(n, m) ==
    /\ <<m, n>> \in Queues
    /\ msgs[<<m, n>>] # << >>
    /\ LET d == Head(msgs[<<m, n>>])
           rest == [msgs EXCEPT ![<<m, n>>] = Tail(@)]
       IN
       IF d + 1 < depth[n]
         THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs' = [q \in Queues |->
                            IF q[1] = n /\ q[2] # m
                              THEN Append(rest[q], d + 1)
                              ELSE rest[q]]
         ELSE /\ msgs' = rest
              /\ UNCHANGED <<depth, parent>>

NodeStep(n) == \E m \in SetNbrs(n) : Receive(n, m)

Stabilized == \A q \in Queues : msgs[q] = << >>

Done == Stabilized /\ UNCHANGED vars

Next == (\E n \in Nodes : NodeStep(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(NodeStep(n))

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: recorded distance never underestimates true distance
Safety == \A n \in Nodes : depth[n] >= Dist(n)

\* Distance semantics: depth is one more than parent's depth (except root/unset)
ParentConsistent ==
    \A n \in Nodes \ {root} :
        depth[n] < Infinity => /\ parent[n] \in SetNbrs(n)
                               /\ depth[parent[n]] < depth[n]

\* Correctness at stabilization
CorrectAtStable ==
    Stabilized =>
        /\ \A n \in Nodes : depth[n] = Dist(n)
        /\ \A n \in Nodes \ {root} :
              /\ parent[n] \in SetNbrs(n)
              /\ depth[n] = depth[parent[n]] + 1

\* Progress: eventually the algorithm stabilizes (and stays so)
Progress == <>[]Stabilized

=============================================================================