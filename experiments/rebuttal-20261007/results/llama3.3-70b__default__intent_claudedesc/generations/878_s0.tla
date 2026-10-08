```
MODULE SpanningTreeAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges, Root, MaxDistance
VARIABLES Parent, Distance

Init ==
  /\ Distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxDistance]
  /\ Parent = [n \in Nodes |-> n]

Next ==
  \/ \E n \in Nodes :
      /\ Distance[n] > 1 + Min({Distance[m] : m \in {x \in Nodes : {n, x} \in Edges}})
      /\ \E d \in Nat :
          /\ 1 + Min({Distance[m] : m \in {x \in Nodes : {n, x} \in Edges}}) < d
          /\ d < Distance[n]
          /\ \E p \in {x \in Nodes : {n, x} \in Edges} :
              /\ Distance[p] = Min({Distance[m] : m \in {x \in Nodes : {n, x} \in Edges}})
              /\ Distance' = [Distance EXCEPT ![n] = d]
              /\ Parent' = [Parent EXCEPT ![n] = p]
      /\ UNCHANGED << >>
  \/ \E n \in Nodes :
      /\ Distance[n] = Min({Distance[m] : m \in {x \in Nodes : {n, x} \in Edges}}) + 1
      /\ Parent[n] \in {x \in Nodes : {n, x} \in Edges}
      /\ UNCHANGED << >>
  \/ UNCHANGED << >>

Spec ==
  Init /\ [][Next]_<<Parent, Distance>>
  /\ WF_<<Parent, Distance>>(Next)

THEOREM Spec => []<>(\A n \in Nodes :
  /\ (n = Root) => (Distance[n] = 0 /\ Parent[n] = n)
  /\ (Distance[n] = MaxDistance) => (Parent[n] = n /\ \A m \in {x \in Nodes : {n, x} \in Edges} : Distance[m] >= Distance[n])
  /\ (Distance[n] # MaxDistance) => (Distance[n] = Distance[Parent[n]] + 1 /\ Parent[n] \in {x \in Nodes : {n, x} \in Edges}))

THEOREM Spec => <>[]~(Enabled(<Next>_<Parent, Distance>))
```