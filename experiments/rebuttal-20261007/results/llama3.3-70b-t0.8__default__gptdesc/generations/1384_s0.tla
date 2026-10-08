```
MODULE BoundedSequencesAndGraphs
EXTENDS Integers, Sequences, TLC
CONSTANTS Graph
VARIABLES x, y

Init ==
  /\ x \in EdgeSet(Graph)
  /\ y \in EdgeSet(Graph)

Next ==
  /\ x' \in EdgeSet(Graph)
  /\ y' \in EdgeSet(Graph)
  /\ (x, y) /= (x', y')

Spec ==
  Init /\ [][Next]_<<x, y>>

TypeInvariant ==
  /\ x \in EdgeSet(Graph)
  /\ y \in EdgeSet(Graph)

GraphCardinalityAssumption ==
  Cardinality(EdgeSet(Graph)) = TLCEval(RandomElement(1..10))

TestGraph ==
  {<<a, b>> \in Graph : a = TLCEval(RandomElement(1..5))}

Invariant ==
  /\ TypeInvariant
  /\ x \in TestGraph
  /\ y \in TestGraph
  /\ Cardinality(TestGraph) = TLCEval(RandomElement(1..10))

THEOREM Spec => []Invariant

Fairness ==
  WF_Vars(Next, <<x, y>>)
```