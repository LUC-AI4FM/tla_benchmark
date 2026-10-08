```
MODULE BoundedSequenceAndGraph
EXTENDS Integers, TLC, Sequences

CONSTANTS Graph

VARIABLES x, y

Init == (* Initialize x and y to arbitrary edges in Graph *)
        /\ x \in Graph
        /\ y \in Graph

Next == (* Update x and y to new edges in Graph *)
        /\ x' \in Graph
        /\ y' \in Graph

Spec == Init /\ [][Next]_<<x, y>>

THEOREM Spec => []<>(x \in Graph /\ y \in Graph)

Inv == (* Type membership and derived test graph membership *)
       /\ x \in Graph
       /\ y \in Graph
       /\ {x, y} \subseteq Graph
       /\ Cardinality({x, y}) = 2

THEOREM Spec => []Inv

Fairness == WF_Vars(Next, <<x, y>>)

TLCEvalCardinalityAssumption ==
  ASSUME Cardinality(Sequences(2, Graph)) <= 10

RandomElementInGraph(x) == CHOOSE e \in Graph : TRUE
```