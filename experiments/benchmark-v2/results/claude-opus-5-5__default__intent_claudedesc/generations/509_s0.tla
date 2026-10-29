---------------------------- MODULE DistributedBFS ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, Root

ASSUME RootInNodes == Root \in Nodes
ASSUME EdgesWellFormed == Edges \subseteq { {a, b} : a \in Nodes, b \in Nodes }

N == Cardinality(Nodes)          \* N serves as "infinity" depth

Nbrs(n) == { m \in Nodes : {m, n} \in Edges /\ m # n }

\* Directed channels: one FIFO queue per ordered pair of adjacent nodes
Ch == { c \in Nodes \X Nodes : {c[1], c[2]} \in Edges /\ c[1] # c[2] }

VARIABLES depth, parent, queue

vars == << depth, parent, queue >>

-----------------------------------------------------------------------------
(* Graph-theoretic shortest-path distance from Root *)

Reach[k \in Nat] ==
    IF k = 0 THEN {Root}
    ELSE Reach[k-1] \cup UNION { Nbrs(m) : m \in Reach[k-1] }

Reachable(n) == \E k \in 0..N : n \in Reach[k]

Dist(n) ==
    IF Reachable(n)
    THEN CHOOSE k \in 0..N : n \in Reach[k] /\ \A j \in 0..(k-1) : n \notin Reach[j]
    ELSE N

(* Iterated parent pointers and tree-path length to Root *)
Anc[k \in Nat] ==
    IF k = 0 THEN [x \in Nodes |-> x]
    ELSE [x \in Nodes |-> parent[Anc[k-1][x]]]

ReachesRoot(n) == \E k \in 0..N : Anc[k][n] = Root

PathLen(n) ==
    IF ReachesRoot(n)
    THEN CHOOSE k \in 0..N : Anc[k][n] = Root /\ \A j \in 0..(k-1) : Anc[j][n] # Root
    ELSE N + 1

-----------------------------------------------------------------------------

StrictlyDecreasing(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] > s[j]

TypeOK ==
    /\ depth \in [Nodes -> 0..N]
    /\ parent \in [Nodes -> Nodes]
    /\ queue \in [Ch -> Seq(0..N)]
    /\ \A c \in Ch : StrictlyDecreasing(queue[c])

Init ==
    /\ depth = [n \in Nodes |-> IF n = Root THEN 0 ELSE N]
    /\ parent = [n \in Nodes |-> n]
    /\ queue = [c \in Ch |-> IF c[1] = Root THEN <<0>> ELSE <<>>]

\* Node n receives a depth message from neighbor m
Receive(m, n) ==
    /\ <<m, n>> \in Ch
    /\ queue[<<m, n>>] # << >>
    /\ LET d == Head(queue[<<m, n>>]) IN
         IF d + 1 < depth[n]
         THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ queue' = [c \in Ch |->
                             IF c = <<m, n>> THEN Tail(queue[c])
                             ELSE IF c[1] = n /\ c[2] # m
                                  THEN Append(queue[c], d + 1)
                                  ELSE queue[c]]
         ELSE /\ queue' = [queue EXCEPT ![<<m, n>>] = Tail(queue[<<m, n>>])]
              /\ UNCHANGED << depth, parent >>

Terminated == \A c \in Ch : queue[c] = << >>

Done == Terminated /\ UNCHANGED vars

Next ==
    \/ \E c \in Ch : Receive(c[1], c[2])
    \/ Done

Spec == Init /\ [][Next]_vars /\ \A c \in Ch : WF_vars(Receive(c[1], c[2]))

-----------------------------------------------------------------------------
(* Correctness properties *)

DepthBounded == \A n \in Nodes : depth[n] >= Dist(n)

Postcondition ==
    Terminated =>
        \A n \in Nodes :
            Reachable(n) =>
                /\ depth[n] = Dist(n)
                /\ PathLen(n) = Dist(n)

Termination == <>Terminated

StableTermination == <>[]Terminated

=============================================================================