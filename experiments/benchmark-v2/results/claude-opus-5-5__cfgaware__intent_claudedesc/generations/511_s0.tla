---------------------------- MODULE DistributedBFS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,      \* set of nodes
          Edges,      \* set of edges, given as ordered pairs <<u, v>> (treated as undirected)
          root,       \* the distinguished root node
          MaxNodes    \* bound on depths; also used as "infinity" (unknown depth)

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat /\ MaxNodes >= 1

VARIABLES depth,   \* depth[n]: currently known distance from the root
          parent,  \* parent[n]: current parent pointer
          msgs     \* msgs[<<u,v>>]: FIFO queue of depth values sent from u to v

vars == <<depth, parent, msgs>>

Nbrs(n) == { m \in Nodes : m # n /\ (<<n, m>> \in Edges \/ <<m, n>> \in Edges) }

Chans == { <<u, v>> \in Nodes \X Nodes : v \in Nbrs(u) }

\* Graph distance from the root, computed by iterating BFS levels
Reach[k \in 0..MaxNodes] ==
    IF k = 0 THEN {root}
    ELSE Reach[k-1] \cup UNION { Nbrs(n) : n \in Reach[k-1] }

Reachable(n) == \E k \in 0..MaxNodes : n \in Reach[k]

Dist(n) ==
    IF Reachable(n)
    THEN CHOOSE k \in 0..MaxNodes : n \in Reach[k] /\ \A j \in 0..(k-1) : n \notin Reach[j]
    ELSE MaxNodes

-------------------------------------------------------------------------------

\* The root initiates: it starts with depth 0 and has sent depth 1 to each neighbor.
Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = [c \in Chans |-> IF c[1] = root /\ 1 < MaxNodes
                                 THEN <<1>> ELSE <<>>]

\* Node v receives depth d from neighbor u
Receive(u, v) ==
    /\ <<u, v>> \in Chans
    /\ msgs[<<u, v>>] # <<>>
    /\ LET d == Head(msgs[<<u, v>>])
           rest == [msgs EXCEPT ![<<u, v>>] = Tail(@)]
       IN  IF d < depth[v]
           THEN /\ depth'  = [depth  EXCEPT ![v] = d]
                /\ parent' = [parent EXCEPT ![v] = u]
                /\ msgs'   = [c \in Chans |->
                                IF c[1] = v /\ c[2] # u /\ d + 1 < MaxNodes
                                THEN Append(rest[c], d + 1)
                                ELSE rest[c]]
           ELSE /\ msgs' = rest
                /\ UNCHANGED <<depth, parent>>

AllEmpty == \A c \in Chans : msgs[c] = <<>>

Done == AllEmpty /\ UNCHANGED vars

Next == (\E u, v \in Nodes : Receive(u, v)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------

TypeOK ==
    /\ depth  \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ DOMAIN msgs = Chans
    /\ \A c \in Chans : \A i \in 1..Len(msgs[c]) : msgs[c][i] \in 1..MaxNodes

\* Messages in transit never carry a depth better than the true distance
MsgOK ==
    \A c \in Chans : \A i \in 1..Len(msgs[c]) : msgs[c][i] >= Dist(c[2])

\* Upon termination, depths equal graph distances and parents form a BFS tree
DepthCorrect ==
    AllEmpty =>
        \A n \in Nodes :
            /\ depth[n] = Dist(n)
            /\ (n # root /\ Reachable(n)) =>
                    /\ parent[n] \in Nbrs(n)
                    /\ depth[parent[n]] = depth[n] - 1

Termination == <>AllEmpty

===============================================================================