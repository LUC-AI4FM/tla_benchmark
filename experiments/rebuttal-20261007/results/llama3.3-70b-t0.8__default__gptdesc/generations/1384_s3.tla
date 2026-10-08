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

Spec == Init /\ [][Next]_<<x, y>>
  
TypeInvariant ==
  /\ x \in EdgeSet(Graph)
  /\ y \in EdgeSet(Graph)

GraphCardinalityAssumption ==
  Cardinality(EdgeSet(Graph)) = 5

TestGraph == Graph

Invariant ==
  /\ TypeInvariant
  /\ {x, y} \subseteq EdgeSet(TestGraph)
  /\ Cardinality({x, y}) = TLCEval(Cardinality({x, y}))

THEOREM Spec => []Invariant
```