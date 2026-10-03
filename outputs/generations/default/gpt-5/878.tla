--------------------------- MODULE RootedSpanningTree ---------------------------

EXTENDS Naturals, Integers

CONSTANTS Node, Root, Edge, MaxCardinality

ASSUME
  /\ Root \in Node
  /\ Edge \subseteq Node \X Node
  /\ \A u \in Node, v \in Node : <<u,v>> \in Edge => <<v,u>> \in Edge
  /\ \A v \in Node : <<v,v>> \notin Edge
  /\ MaxCardinality \in Nat

VARIABLES mom, dist

Adj(u, v) == <<u, v>> \in Edge

TypeInv ==
  /\ mom \in [Node -> Node]
  /\ dist \in [Node -> 0..MaxCardinality]

Init ==
  /\ TypeInv
  /\ mom = [n \in Node |-> n]
  /\ dist = [n \in Node |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E x \in Node, y \in Node, d \in 0..MaxCardinality :
    /\ Adj(x, y)
    /\ dist[y] < dist[x]
    /\ dist[y] <= d /\ d < dist[x]
    /\ mom' = [mom EXCEPT ![x] = y]
    /\ dist' = [dist EXCEPT ![x] = d]

Vars == << mom, dist >>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Next)

Stable ==
  \A x \in Node :
    \A y \in Node :
      Adj(x, y) => dist[y] >= dist[x]

Post ==
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A v \in Node \ {Root} :
       IF dist[v] = MaxCardinality
       THEN mom[v] = v
       ELSE /\ Adj(v, mom[v])
            /\ dist[mom[v]] + 1 = dist[v]

Safety ==
  [] (Stable => Post)

Termination ==
  <> [] Stable

AllEventualRootParent ==
  \A v \in Node : <> (mom[v] = Root)

=============================================================================