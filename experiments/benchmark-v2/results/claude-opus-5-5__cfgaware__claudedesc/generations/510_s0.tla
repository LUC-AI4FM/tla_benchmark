---------------------------- MODULE ShortestPaths ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

ASSUME /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes
       /\ \A e \in Edges : \E a, b \in Nodes : a # b /\ e = {a, b}
       /\ \A n \in Nodes :
             \E k \in 1..MaxNodes :
               \E p \in [1..k -> Nodes] :
                  /\ p[1] = root
                  /\ p[k] = n
                  /\ \A i \in 1..(k-1) : {p[i], p[i+1]} \in Edges

VARIABLES msgs, depth, parent

vars == <<msgs, depth, parent>>

SetNbrs(n) == {m \in Nodes : {m, n} \in Edges}

Queues == {<<m, n>> \in Nodes \X Nodes : {m, n} \in Edges}

Init ==
  /\ msgs = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]
  /\ depth = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ parent = [n \in Nodes |-> n]

N(n) ==
  \E m \in SetNbrs(n) :
     /\ msgs[<<m, n>>] # <<>>
     /\ LET d == Head(msgs[<<m, n>>]) IN
          IF d + 1 < depth[n]
            THEN /\ depth' = [depth EXCEPT ![n] = d + 1]
                 /\ parent' = [parent EXCEPT ![n] = m]
                 /\ msgs' = [q \in Queues |->
                               IF q = <<m, n>>
                                 THEN Tail(msgs[q])
                               ELSE IF q[1] = n /\ q[2] # m
                                 THEN Append(msgs[q], d + 1)
                               ELSE msgs[q]]
            ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = Tail(@)]
                 /\ UNCHANGED <<depth, parent>>

Next == \E n \in Nodes : N(n)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(N(n))

=============================================================================