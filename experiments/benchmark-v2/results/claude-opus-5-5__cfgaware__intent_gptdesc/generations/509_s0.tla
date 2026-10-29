------------------------------ MODULE SpanningTreeTermination ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes,     \* finite set of node identifiers
          Edges,     \* set of pairs <<a, b>>; the network is undirected
          root,      \* designated root node
          MaxNodes   \* bound on depths; must be >= Cardinality(Nodes)

ASSUME /\ root \in Nodes
       /\ Edges \subseteq (Nodes \X Nodes)
       /\ MaxNodes \in Nat
       /\ MaxNodes >= Cardinality(Nodes)

VARIABLES depth,   \* depth[n] : current depth estimate (MaxNodes = "infinity")
          parent,  \* parent[n] : current parent pointer
          msgs     \* msgs[<<a,b>>] : FIFO queue of depth values sent from a to b

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
(* Topology *)

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges \/ <<m, n>> \in Edges }

\* Directed communication channels, one per direction of every edge.
Chan == { c \in Nodes \X Nodes : c[2] \in Nbrs(c[1]) }

\* Layer[k] = set of nodes at graph distance <= k from root.
Layer[k \in 0..MaxNodes] ==
    IF k = 0 THEN {root}
    ELSE Layer[k-1] \cup { n \in Nodes : Nbrs(n) \cap Layer[k-1] # {} }

\* Graph distance (number of hops) from n to root.
Dist(n) ==
    IF n \in Layer[MaxNodes]
    THEN CHOOSE k \in 0..MaxNodes : n \in Layer[k] /\ (k = 0 \/ n \notin Layer[k-1])
    ELSE MaxNodes

Connected == \A n \in Nodes : n \in Layer[MaxNodes]

-----------------------------------------------------------------------------
(* Helper predicates *)

StrictlyDecreasing(s) == \A i \in 1..(Len(s) - 1) : s[i] > s[i+1]

Quiescent == \A c \in Chan : msgs[c] = << >>

RECURSIVE Up(_, _)
Up(n, k) == IF k = 0 THEN n ELSE Up(parent[n], k - 1)

-----------------------------------------------------------------------------
(* Initial state: root has depth 0 and announces it to all its neighbors. *)

Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> root]
    /\ msgs   = [c \in Chan |-> IF c[1] = root THEN <<0>> ELSE << >>]

(* Node n receives the head d of the queue from neighbor m.  If d + 1 improves
   its depth, it adopts m as parent and announces its new depth to all its
   neighbors; otherwise the message is simply discarded. *)
Receive(m, n) ==
    /\ <<m, n>> \in Chan
    /\ msgs[<<m, n>>] # << >>
    /\ LET d == Head(msgs[<<m, n>>]) IN
         IF d + 1 < depth[n]
         THEN /\ depth'  = [depth  EXCEPT ![n] = d + 1]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs'   = [c \in Chan |->
                              IF c = <<m, n>> THEN Tail(msgs[c])
                              ELSE IF c[1] = n THEN Append(msgs[c], d + 1)
                              ELSE msgs[c]]
         ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = Tail(@)]
              /\ UNCHANGED <<depth, parent>>

\* Stuttering once quiescent (avoids spurious deadlock reports).
Done == Quiescent /\ UNCHANGED vars

Next == (\E m, n \in Nodes : Receive(m, n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

MsgInv ==
    \A c \in Chan :
        /\ StrictlyDecreasing(msgs[c])
        /\ \A i \in 1..Len(msgs[c]) : msgs[c][i] >= depth[c[1]]

TypeOK ==
    /\ depth \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ \A n \in Nodes : parent[n] \in Nbrs(n) \cup {root}
    /\ depth[root] = 0
    /\ msgs \in [Chan -> Seq(0..MaxNodes)]
    /\ \A c \in Chan : Len(msgs[c]) <= MaxNodes
    /\ MsgInv

(* Final postcondition: at quiescence, depths are graph distances, parent
   pointers form a tree rooted at root, and following parent pointers from
   any node reaches root in exactly depth hops. *)
DepthCorrect ==
    Quiescent =>
        \A n \in Nodes :
            /\ depth[n] = Dist(n)
            /\ (n # root) => /\ parent[n] \in Nbrs(n)
                             /\ depth[parent[n]] = depth[n] - 1
            /\ Up(n, depth[n]) = root

-----------------------------------------------------------------------------
(* Liveness: global quiescence is eventually reached. *)

Termination == <>Quiescent

=============================================================================