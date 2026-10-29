------------------------------ MODULE SpanTree ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, MaxCardinality, Root

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES parent, dist, msgs

vars == <<parent, dist, msgs>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

\* Within[k] is the set of nodes at hop distance at most k from Root.
Within[k \in 0..MaxCardinality] ==
    IF k = 0 THEN {Root}
             ELSE Within[k-1] \cup UNION {Nbrs(n) : n \in Within[k-1]}

Reachable == Within[MaxCardinality]

HopDist(n) ==
    CHOOSE k \in 0..MaxCardinality :
        /\ n \in Within[k]
        /\ (k = 0 \/ n \notin Within[k-1])

\* A message <<from, to, d>> means node "from" told neighbor "to" its distance is d.
Messages == Nodes \X Nodes \X (0..MaxCardinality)

TypeOK ==
    /\ parent \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]
    /\ msgs \subseteq Messages

Init ==
    /\ parent = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
    /\ msgs = {<<Root, n, 0>> : n \in Nbrs(Root)}

\* Node n receives distance d from neighbor m.
Receive(n, m, d) ==
    /\ <<m, n, d>> \in msgs
    /\ IF d + 1 < dist[n]
         THEN /\ dist' = [dist EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs' = (msgs \ {<<m, n, d>>})
                           \cup {<<n, k, d + 1>> : k \in Nbrs(n)}
         ELSE /\ msgs' = msgs \ {<<m, n, d>>}
              /\ UNCHANGED <<dist, parent>>

Terminated == msgs = {}

\* Quiesced: the algorithm has no local step enabled.
Done == Terminated /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes, m \in Nodes, d \in 0..MaxCardinality : Receive(n, m, d)
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PostCondition ==
    \A n \in Nodes :
        IF n \in Reachable
          THEN /\ dist[n] = HopDist(n)
               /\ (n = Root) => (parent[n] = Root)
               /\ (n # Root) => /\ parent[n] \in Nbrs(n)
                                /\ dist[parent[n]] = dist[n] - 1
          ELSE /\ parent[n] = n
               /\ dist[n] = MaxCardinality

Safety == Terminated => PostCondition

Liveness == <>[]Terminated

=============================================================================