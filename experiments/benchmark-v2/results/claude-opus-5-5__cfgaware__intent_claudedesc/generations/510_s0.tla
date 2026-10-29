------------------------------- MODULE DistributedSPT -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

ASSUME RootInNodes == root \in Nodes
ASSUME EdgesWellFormed ==
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2
ASSUME MaxNodesBound == MaxNodes \in Nat /\ MaxNodes >= Cardinality(Nodes)

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

SetNbrs(n) == {m \in Nodes : {m, n} \in Edges}

Queues == {<<m, n>> \in Nodes \X Nodes : {m, n} \in Edges}

\* Reference shortest-path distance (in hops) from the root
RECURSIVE ReachIn(_, _)
ReachIn(S, k) == IF k = 0 THEN S
                 ELSE ReachIn(S \cup UNION {SetNbrs(x) : x \in S}, k - 1)

Dist(n) == CHOOSE k \in 0..MaxNodes :
               /\ n \in ReachIn({root}, k)
               /\ \A j \in 0..MaxNodes : n \in ReachIn({root}, j) => k <= j

TypeOK ==
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs \in [Queues -> Seq(0..MaxNodes)]

Init ==
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]

Proc(n) ==
    \E m \in SetNbrs(n) :
        /\ msgs[<<m, n>>] # <<>>
        /\ LET d == Head(msgs[<<m, n>>])
               better == d + 1 < depth[n]
           IN
           /\ depth' = IF better THEN [depth EXCEPT ![n] = d + 1] ELSE depth
           /\ parent' = IF better THEN [parent EXCEPT ![n] = m] ELSE parent
           /\ msgs' = [q \in Queues |->
                         IF q = <<m, n>> THEN Tail(msgs[q])
                         ELSE IF better /\ q[1] = n
                              THEN Append(msgs[q], d + 1)
                              ELSE msgs[q]]

Next == \E n \in Nodes : Proc(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Proc(n))

Stable == \A q \in Queues : msgs[q] = <<>>

Termination == <>[]Stable

CorrectDistances == Stable => \A n \in Nodes : depth[n] = Dist(n)

ValidTree ==
    Stable =>
        /\ parent[root] = root
        /\ \A n \in Nodes \ {root} :
              /\ parent[n] \in SetNbrs(n)
              /\ depth[parent[n]] < depth[n]

DepthNonIncreasing == [][\A n \in Nodes : depth'[n] <= depth[n]]_vars

=====================================================================================