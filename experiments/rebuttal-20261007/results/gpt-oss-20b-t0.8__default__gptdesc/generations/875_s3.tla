MODULE RandomSpanningTree
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

Edges == [ n \in Nodes |-> CHOOSE S \in SUBSET (Nodes \ {n}) : TRUE ]

TypeInvariant ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]

Init ==
  /\ TypeInvariant
  /\ mom = [n \in Nodes |-> n]
  /\ dist = ([Root |-> 0] \u [n \in Nodes \ {Root} |-> 1])

Next ==
  \E i \in Nodes :
    \E j \in Edges[i] :
      /\ dist[j] < dist[i]
      /\ \E newD \in Nat :
           /\ dist[j] < newD
           /\ newD < dist[i]
           /\ mom' = [mom EXCEPT ![i] = j]
           /\ dist' = [dist EXCEPT ![i] = newD]

Quiescent ==
  \A i \in Nodes : \A j \in Edges[i] :
    dist[i] <= dist[j] + 1

Post ==
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A n \in Nodes :
        IF n = Root THEN TRUE
        ELSE IF mom[n] = n THEN dist[n] > 0
        ELSE
          /\ mom[n] \in Edges[n]
          /\ dist[mom[n]] < dist[n]

Safety ==
  Quiescent => Post

Spec == Init /\ [] [Next]_vars /\ WF_vars(Next)

Liveness == []<>(Post)

THEOREM Spec_implies_Safety : Spec => Safety
THEOREM Spec_implies_Liveness : Spec => Liveness