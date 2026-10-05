---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxCardinality

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) == {m \in Nodes : \E e \in Edges : e = {n, m}}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> 0..MaxCardinality]

Init == /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]
        /\ mom = [n \in Nodes |-> n]

Update(n, m) == 
    /\ m \in Neighbors(n)
    /\ dist[m] + 1 < dist[n]
    /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
        dist' = [dist EXCEPT ![n] = d]
    /\ mom' = [mom EXCEPT ![n] = m]

Next == \E n \in Nodes : \E m \in Nodes : Update(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Reachable(n) == 
    LET RECURSIVE ReachableFrom(_)
        ReachableFrom(S) == 
            LET New == {m \in Nodes : \E s \in S : m \in Neighbors(s)} \ S
            IN IF New = {} THEN S ELSE ReachableFrom(S \cup New)
    IN n \in ReachableFrom({Root})

PostCondition ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A n \in Nodes :
        IF n = Root THEN TRUE
        ELSE IF ~Reachable(n) THEN
            /\ dist[n] = MaxCardinality
            /\ mom[n] = n
            /\ \A m \in Neighbors(n) : dist[m] = MaxCardinality
        ELSE
            /\ dist[n] = dist[mom[n]] + 1
            /\ mom[n] \in Neighbors(n)

Terminated == ~ENABLED Next

Safety == Terminated => PostCondition

Liveness == <>Terminated

=============================================================================