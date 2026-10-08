```
MODULE BoundedSequencesAndGraphs
EXTENDS Integers, FiniteSets, TLC
CONSTANTS Graph
VARIABLES x, y

Init == (* Initial condition: both variables are arbitrary edges in the graph *)
        /\ x \in Graph
        /\ y \in Graph

Next == (* Next state relation: either variable can change to any edge in the graph *)
        \/ x' \in Graph
        \/ y' \in Graph

Spec == Init /\ [][Next]_<<x, y>>

THEOREM Spec => []((x \in Graph) /\ (y \in Graph))
            /\ (Cardinality({<<x, y>> \in Graph : TRUE}) = 5)

Inv == (x \in Graph) /\ (y \in Graph)
        /\ {x, y} \subseteq Graph
        /\ Cardinality({z \in {x, y} : z \in Graph}) = 2

Fairness == WF_Vars(Next, <<x, y>>)

TLCEvalCardinality == 
  LET CountEdges == {e \in Graph : TRUE}
  IN  Cardinality(CountEdges) = 5
```