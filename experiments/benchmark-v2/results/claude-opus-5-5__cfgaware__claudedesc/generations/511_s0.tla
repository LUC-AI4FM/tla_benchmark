---------------------------- MODULE MCSession10set ----------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Graph topology: six nodes, a distinguished root, six undirected edges.  *)
(***************************************************************************)
Nodes    == {1, 2, 3, 4, 5, 6}
root     == 1
Edges    == { {1,2}, {1,3}, {2,4}, {3,4}, {4,5}, {5,6} }
MaxNodes == 6

VARIABLES depth, parent, msgs

vars == << depth, parent, msgs >>

Nbrs(n) == { m \in Nodes : {m, n} \in Edges }

\* Directed channels between adjacent nodes: <<sender, receiver>>
Channels == { p \in Nodes \X Nodes : {p[1], p[2]} \in Edges }

Depths == 0..MaxNodes

TypeOK ==
    /\ depth  \in [Nodes -> Depths]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \in [Channels -> SUBSET Depths]
    \* Every queued depth is at least one more than the sender's current depth
    /\ \A c \in Channels : \A d \in msgs[c] : d >= depth[c[1]] + 1

Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = [c \in Channels |-> IF c[1] = root THEN {1} ELSE {}]

\* Node n receives depth d from neighbor m
Receive(m, n) ==
    /\ <<m, n>> \in Channels
    /\ \E d \in msgs[<<m, n>>] :
         IF d < depth[n]
         THEN /\ depth'  = [depth  EXCEPT ![n] = d]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs'   = [c \in Channels |->
                              IF c = <<m, n>>
                                THEN (IF n = c[1] /\ m \in Nbrs(n)
                                        THEN msgs[c] \ {d}
                                        ELSE msgs[c] \ {d})
                              ELSE IF c[1] = n
                                THEN msgs[c] \cup {d + 1}
                              ELSE msgs[c]]
         ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
              /\ UNCHANGED << depth, parent >>

Next == \E m, n \in Nodes : Receive(m, n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* True shortest-path distances from the root.                             *)
(***************************************************************************)
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {root}
            ELSE Reach(k - 1) \cup { n \in Nodes : \E m \in Reach(k - 1) : {m, n} \in Edges }

Dist(n) == CHOOSE k \in 0..MaxNodes :
               /\ n \in Reach(k)
               /\ (k = 0 \/ n \notin Reach(k - 1))

\* Length of the path from n to the root following parent pointers
RECURSIVE PathLen(_, _)
PathLen(n, k) == IF n = root THEN 0
                 ELSE IF k = 0 THEN MaxNodes + 1
                 ELSE 1 + PathLen(parent[n], k - 1)

AllEmpty == \A c \in Channels : msgs[c] = {}

DepthCorrect ==
    AllEmpty => \A n \in Nodes : PathLen(n, MaxNodes) = Dist(n)

Termination == <>AllEmpty

=============================================================================