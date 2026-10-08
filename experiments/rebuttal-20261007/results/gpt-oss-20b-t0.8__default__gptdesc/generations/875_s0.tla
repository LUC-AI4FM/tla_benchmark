--------------------------- MODULE SpanningTreeSpec ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

(* Random graph generation *)
Edges == [ n \in Nodes |-> RandomSubset(Nodes \ {n}) ]

VARIABLES mom, dist

Init ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> Nat]
  /\ \A n \in Nodes : mom[n] = n
  /\ \A n \in Nodes :
        IF n = Root THEN dist[n] = 0 ELSE dist[n] = 1

Next ==
  \E u \in Nodes :
    \E v \in Edges[u] :
      /\ dist[v] < dist[u]
      /\ \E nd \in Nat : (dist[v] < nd) /\ (nd < dist[u]) 
           /\ mom' = [mom EXCEPT ![u] = v]
           /\ dist' = [dist EXCEPT ![u] = nd]

TypeInvariant ==
  mom \in [Nodes -> Nodes] /\ dist \in [Nodes -> Nat]

(* Postcondition: rooted spanning tree or unreachable nodes *)
Post ==
  /\ mom[Root] = Root
  /\ dist[Root] = 0
  /\ \A n \in Nodes :
        IF n = Root THEN TRUE
        ELSE
          \/ (mom[n] = n /\ dist[n] > 0)
          \/ (mom[n] \in Edges[n] /\ dist[n] = dist[mom[n]] + 1)

(* Quiescence: no possible Next action *)
Quiescent ==
  \A n \in Nodes :
    \A v \in Edges[n] :
      NOT (dist[v] < dist[n]) \/ (dist[v] + 1 >= dist[n])

Safety == [] (Quiescent => Post)

Liveness == <> Post

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM TypeInvariant_Is_Valid: Spec => []TypeInvariant
THEOREM Safety_Is_Valid: Spec => Safety
THEOREM Liveness_Holds: Spec => Liveness
=============================================================================