----------------------------- MODULE RandomSpanningTree -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES mom, dist

vars == << mom, dist >>

Adj ==
  [ n \in Nodes |->
      { m \in (Nodes \ {n}) : RandomElement({TRUE, FALSE}) } ]

Edges ==
  { {u, v} :
      u \in Nodes /\ v \in Nodes /\ u # v /\ (v \in Adj[u] \/ u \in Adj[v]) }

Neighbors(n) == { m \in Nodes : m # n /\ {n, m} \in Edges }

TypeOK == mom \in [Nodes -> Nodes] /\ dist \in [Nodes -> Nat] /\ Root \in Nodes

Init ==
  TypeOK
  /\ \A n \in Nodes : mom[n] = n
  /\ dist[Root] = 0
  /\ \A n \in (Nodes \ {Root}) : dist[n] \in Nat \ {0}

Next ==
  \E n \in Nodes, p \in Nodes, d \in Nat :
    n # p /\ {n, p} \in Edges /\ dist[p] < d /\ d < dist[n]
    /\ mom' = [mom EXCEPT ![n] = p]
    /\ dist' = [dist EXCEPT ![n] = d]

Quiescent ==
  ~(\E n \in Nodes, p \in Nodes :
      n # p /\ {n, p} \in Edges /\ dist[p] < dist[n]
      /\ \E d \in Nat : dist[p] < d /\ d < dist[n])

RECURSIVE ReachIter(_)
Step(S) == S \cup { v \in Nodes : \E u \in S : {u, v} \in Edges }
ReachIter(0) == {Root}
ReachIter(n) == Step(ReachIter(n - 1))

MaxDepth == Cardinality(Nodes)

Reachable == UNION { ReachIter(k) : k \in 0..MaxDepth }

RECURSIVE ParentPow(_, _)
ParentPow(n, 0) == n
ParentPow(n, k) == mom[ParentPow(n, k - 1)]

Post ==
  mom[Root] = Root /\ dist[Root] = 0
  /\ \A n \in (Nodes \ {Root}) :
       IF n \in Reachable
       THEN \E k \in 1..MaxDepth :
              ParentPow(n, k) = Root
              /\ \A i \in 0..(k - 1) :
                    LET x == ParentPow(n, i)
                        y == ParentPow(n, i + 1)
                    IN {x, y} \in Edges /\ dist[y] < dist[x]
       ELSE mom[n] = n

Safety == [](Quiescent => Post)

TypeSafety == []TypeOK

Liveness == <>Post

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================