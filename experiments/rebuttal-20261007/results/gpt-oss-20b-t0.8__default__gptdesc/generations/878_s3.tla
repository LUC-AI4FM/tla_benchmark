```
MODULE RootedSpanningTree
EXTENDS Naturals, TLC

CONSTANTS NODES, ROOT, Adj, MaxCardinality

VARIABLES mom, dist

Init ==
  /\ mom = [n \in NODES |-> n]
  /\ dist = [n \in NODES |
              IF n = ROOT THEN 0 ELSE MaxCardinality]

Next ==
  ∃ i, j \in NODES :
    /\ (i,j) ∈ Adj
    /\ dist[j] < dist[i]
    /\ ∃ newd ∈ Nat :
          /\ dist[j] < newd
          /\ newd < dist[i]
          /\ mom' = [mom EXCEPT ![i] = j]
          /\ dist' = [dist EXCEPT ![i] = newd]

NoImprovement == ∀ n \in NODES : ¬∃ j \in NODES : (n,j) ∈ Adj /\ dist[j] < dist[n]

PostCond ==
  /\ mom[ROOT] = ROOT
  /\ dist[ROOT] = 0
  /\ ∀ n \in NODES :
        n # ROOT => 
          /\ ∃ p \in NODES : (n,p) ∈ Adj /\ mom[n] = p
          /\ dist[n] = dist[p] + 1

Safety == [] (NoImprovement => PostCond)

LivenessTermination == ◇ NoImprovement

RootParentProperty ==
  ∀ n \in NODES : ◇ (mom[n] = ROOT)

Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_vars(Next)
```