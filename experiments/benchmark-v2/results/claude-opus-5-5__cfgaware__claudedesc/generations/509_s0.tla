------------------------------ MODULE MCSession10 ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Graph constants: six nodes, six undirected edges, root "r"
Nodes == {"r", "a", "b", "c", "d", "e"}

Edges == { {"r", "a"}, {"r", "b"}, {"a", "c"},
           {"b", "c"}, {"c", "d"}, {"d", "e"} }

root == "r"

MaxNodes == 6

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

Queues == {q \in Nodes \X Nodes : {q[1], q[2]} \in Edges}

-----------------------------------------------------------------------------
Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]

Receive(s, t) ==
    LET q == <<s, t>>
    IN  /\ q \in Queues
        /\ msgs[q] # <<>>
        /\ LET d == Head(msgs[q])
           IN  IF d + 1 < depth[t]
                 THEN /\ depth'  = [depth  EXCEPT ![t] = d + 1]
                      /\ parent' = [parent EXCEPT ![t] = s]
                      /\ msgs'   = [r \in Queues |->
                                      IF r = q THEN Tail(msgs[r])
                                      ELSE IF r[1] = t
                                             THEN Append(msgs[r], d + 1)
                                             ELSE msgs[r]]
                 ELSE /\ msgs' = [msgs EXCEPT ![q] = Tail(msgs[q])]
                      /\ UNCHANGED <<depth, parent>>

Next == \E s, t \in Nodes : Receive(s, t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
TypeOK ==
    /\ depth  \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ DOMAIN msgs = Queues
    /\ \A q \in Queues :
         /\ msgs[q] \in Seq(0..MaxNodes)
         /\ Len(msgs[q]) <= MaxNodes + 1
         /\ \A i \in 1..(Len(msgs[q]) - 1) : msgs[q][i] > msgs[q][i + 1]
         /\ \A i \in 1..Len(msgs[q]) : msgs[q][i] >= depth[q[1]]

\* Path from node n to the root following parent pointers (bounded by fuel)
RECURSIVE PathK(_, _)
PathK(n, k) ==
    IF n = root \/ k = 0
      THEN <<n>>
      ELSE <<n>> \o PathK(parent[n], k - 1)

PPath(n) == PathK(n, MaxNodes)

\* Nodes within k hops of m
RECURSIVE Within(_, _)
Within(m, k) ==
    IF k = 0
      THEN {m}
      ELSE LET W == Within(m, k - 1)
           IN  W \cup {y \in Nodes : \E x \in W : {x, y} \in Edges}

Dist(m, n) ==
    CHOOSE k \in 0..MaxNodes :
        /\ n \in Within(m, k)
        /\ (k = 0 \/ n \notin Within(m, k - 1))

DistanceFrom(m) == [n \in Nodes |-> Dist(m, n)]

AllEmpty == \A q \in Queues : msgs[q] = <<>>

DepthCorrect ==
    AllEmpty =>
        \A n \in Nodes :
            /\ PPath(n)[Len(PPath(n))] = root
            /\ Len(PPath(n)) - 1 = DistanceFrom(root)[n]

Termination == <>(AllEmpty)

=============================================================================