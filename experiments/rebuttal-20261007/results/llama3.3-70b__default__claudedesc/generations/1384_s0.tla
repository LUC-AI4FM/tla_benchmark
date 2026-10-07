```
MODULE Github648
EXTENDS Integers, TLC
CONSTANTS Graph
VARIABLES v, w

BoundedSeq(S, n) == {<<s1, ..., sn>> : s1 \in S, ..., sn \in S, n <= Len(<<s1, ..., sn>>) <= n}
BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

DirectedGraphs(nodes) == 
  { [x |-> {}] : x \in nodes } 
  \* { AddEdge(g, x, y) : g \in DirectedGraphs(nodes), x \in nodes, y \in nodes }
AddEdge(g, x, y) == [g EXCEPT ![x] = g[x] \cup {y}]

TestGraph == LET RE == RandomElement(DirectedGraphs({1, 2, 3})) IN
  TLCEval([RE EXCEPT ![1] = RE[1] \cup {1}])

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1, 2}, 2), 2)) = 57

Inv == 
  /\ v \in Graph.edges
  /\ w \in TestGraph.edges
  /\ TLCEval(TLCEval(Cardinality(BoundedSeqTLCEval(BoundedSeq({1, 2, 3}, 3), 3))) = 65641)

Init == 
  /\ v \in Graph.edges
  /\ w \in Graph.edges

Next == 
  /\ v' \in Graph.edges
  /\ w' \in Graph.edges

Spec == Init /\ [][Next]_<<v, w>>
THEOREM Spec => []Inv
```