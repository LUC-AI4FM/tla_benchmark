MODULE RootedSpanningTree

EXTENDS Naturals

CONSTANTS
  Nodes,
  Adj,   \* adjacency function: [Nodes -> SUBSET Nodes]
  Root,
  MaxDist

VARIABLES mom, dist

(* Initial state *)
Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDist]

(* Transition relation *)
Next ==
  \E i \in Nodes :
    \E j \in Adj[i] :
      /\ dist[j] + 1 < dist[i]
      /\ \E newD \in {dist[j]+1 .. dist[i]-1} :
          /\ mom' = [mom EXCEPT ![i] = j]
          /\ dist' = [dist EXCEPT ![i] = newD]

(* No more updates possible *)
NoMoreUpdates ==
  \A i \in Nodes : \A j \in Adj[i] : dist[j] >= dist[i]

(* Safety invariant: when no updates, we have a rooted spanning tree *)
SafetyInvariant ==
  \A n \in Nodes :
    IF n = Root THEN
      mom[n] = Root /\ dist[n] = 0
    ELSE
      /\ mom[n] \in Adj[n]
      /\ dist[n] = dist[mom[n]] + 1

(* Specification with weak fairness on Next *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM Termination:
  Spec => <> NoMoreUpdates

THEOREM TreeProperty:
  Spec => [] (NoMoreUpdates => SafetyInvariant)

THEOREM RootParent:
  Spec => <> (\A n \in Nodes : mom[n] = Root)

END RootedSpanningTree