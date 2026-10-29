------------------------------ MODULE ShortestPathsToRoot ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachFrom(_, _)
ReachFrom(S, k) ==
    IF k = 0 THEN S
    ELSE ReachFrom(S \cup UNION {Nbrs(x) : x \in S}, k - 1)

ASSUME /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes
       /\ \A e \in Edges : /\ e \subseteq Nodes
                           /\ Cardinality(e) = 2
       /\ ReachFrom({root}, MaxNodes) = Nodes

\* Directed queues: one per ordered pair of adjacent nodes
Queues == {<<m, n>> \in Nodes \X Nodes : {m, n} \in Edges}

VARIABLES msgs, depth, parent

vars == <<msgs, depth, parent>>

TypeOK ==
    /\ msgs \in [Queues -> Seq(0 .. MaxNodes)]
    /\ depth \in [Nodes -> 0 .. MaxNodes]
    /\ parent \in [Nodes -> Nodes]

Init ==
    /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]

Receive(n) ==
    \E m \in Nbrs(n) :
        /\ msgs[<<m, n>>] # <<>>
        /\ LET d == Head(msgs[<<m, n>>]) IN
             IF depth[n] >= d + 2
               THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
                    /\ parent' = [parent EXCEPT ![n] = m]
                    /\ msgs' = [q \in Queues |->
                                  IF q = <<m, n>> THEN Tail(msgs[q])
                                  ELSE IF q[1] = n /\ q[2] # m
                                         THEN Append(msgs[q], d + 1)
                                         ELSE msgs[q]]
               ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = Tail(@)]
                    /\ UNCHANGED <<depth, parent>>

Next == \E n \in Nodes : Receive(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Receive(n))

=============================================================================