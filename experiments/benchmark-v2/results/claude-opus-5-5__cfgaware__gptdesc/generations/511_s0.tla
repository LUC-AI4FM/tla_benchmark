---------------------------- MODULE MCSession10set ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

ASSUME root \in Nodes
ASSUME MaxNodes \in Nat /\ MaxNodes >= Cardinality(Nodes)
ASSUME Edges \subseteq (Nodes \X Nodes)

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

Nbrs(n) == {m \in Nodes : <<n, m>> \in Edges \/ <<m, n>> \in Edges}

Msg == [src : Nodes, d : 0..MaxNodes]

-----------------------------------------------------------------------------

Init ==
    /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
    /\ parent = [n \in Nodes |-> n]
    /\ msgs   = [n \in Nodes |->
                    IF n \in Nbrs(root)
                       THEN << [src |-> root, d |-> 0] >>
                       ELSE << >>]

Receive(n) ==
    /\ msgs[n] # << >>
    /\ LET m == Head(msgs[n]) IN
         IF m.d + 1 < depth[n]
            THEN /\ depth'  = [depth  EXCEPT ![n] = m.d + 1]
                 /\ parent' = [parent EXCEPT ![n] = m.src]
                 /\ msgs'   = [k \in Nodes |->
                                 IF k = n THEN Tail(msgs[n])
                                 ELSE IF k \in Nbrs(n)
                                      THEN Append(msgs[k], [src |-> n, d |-> m.d + 1])
                                      ELSE msgs[k]]
            ELSE /\ msgs' = [msgs EXCEPT ![n] = Tail(msgs[n])]
                 /\ UNCHANGED <<depth, parent>>

-----------------------------------------------------------------------------

Termination == \A n \in Nodes : msgs[n] = << >>

Done == Termination /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

-----------------------------------------------------------------------------

TypeOK ==
    /\ depth  \in [Nodes -> 0..MaxNodes]
    /\ parent \in [Nodes -> Nodes]
    /\ msgs   \in [Nodes -> Seq(Msg)]

\* Length of the parent path from n to root (MaxNodes if root is not reached)
RECURSIVE PathDepth(_, _)
PathDepth(n, fuel) ==
    IF n = root THEN 0
    ELSE IF fuel = 0 THEN MaxNodes
    ELSE LET r == PathDepth(parent[n], fuel - 1)
         IN IF r >= MaxNodes THEN MaxNodes ELSE 1 + r

\* Set of nodes within k hops of root
RECURSIVE Within(_)
Within(k) ==
    IF k = 0 THEN {root}
    ELSE Within(k - 1) \cup {m \in Nodes : \E x \in Within(k - 1) : x \in Nbrs(m)}

\* Graph distance from root (MaxNodes if unreachable)
Distance(n) ==
    IF \E k \in 0..MaxNodes : n \in Within(k)
       THEN CHOOSE k \in 0..MaxNodes :
               /\ n \in Within(k)
               /\ (k = 0 \/ n \notin Within(k - 1))
       ELSE MaxNodes

DepthCorrect ==
    Termination => \A n \in Nodes : PathDepth(n, MaxNodes) = Distance(n)

=============================================================================