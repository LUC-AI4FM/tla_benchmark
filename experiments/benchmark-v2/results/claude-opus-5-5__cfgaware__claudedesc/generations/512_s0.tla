---------------------------- MODULE Session10set ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

SetNbrs(n) == {m \in Nodes : {m, n} \in Edges}

Queues == {<<m, n>> \in Nodes \X Nodes : {m, n} \in Edges}

Reach[k \in 0..MaxNodes] ==
    IF k = 0 THEN {root}
    ELSE Reach[k-1] \cup {m \in Nodes : \E n \in Reach[k-1] : {m, n} \in Edges}

ASSUME /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
       /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes
       /\ Reach[MaxNodes] = Nodes

VARIABLES msgs, depth, parent

vars == <<msgs, depth, parent>>

Init ==
    /\ msgs = [q \in Queues |-> IF q[1] = root THEN {0} ELSE {}]
    /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]

Node(n) ==
    \E m \in SetNbrs(n) :
      \E d \in msgs[<<m, n>>] :
        IF d + 1 < depth[n]
        THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
             /\ parent' = [parent EXCEPT ![n] = m]
             /\ msgs' = [q \in Queues |->
                          IF q = <<m, n>> THEN msgs[q] \ {d}
                          ELSE IF q[1] = n /\ q[2] # m
                               THEN msgs[q] \cup {d + 1}
                               ELSE msgs[q]]
        ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
             /\ UNCHANGED <<depth, parent>>

Next == \E n \in Nodes : Node(n)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Node(n))

=============================================================================