MODULE GraphSpec
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* CONSTANTS *)
CONSTANTS Graph   \* A set of directed edges represented as tuples <<src,dst>>

(* Helper operator for a bounded set of integers from 1 to n *)
BoundedSet(n) == { i \in 1..n }

(* Derived graph filtering edges whose source and destination are distinct *)
DerivedGraph == { e \in Graph : e[1] # e[2] }

(* Variables representing current edges in the system *)
VAR v1, v2

(* Initial state: both variables hold arbitrary edges from the base graph *)
Init ==
    /\ v1 \in Graph
    /\ v2 \in Graph

(* Next-state relation: one of the variables may change to any edge of the graph *)
Next ==
    \/ /\ v1' \in Graph
       /\ v2' = v2
   \/ /\ v1' = v1
       /\ v2' \in Graph

(* Safety invariant ensuring type membership and derived-graph membership *)
TypeInv ==
    /\ v1 \in Graph
    /\ v2 \in Graph
    /\ v1 \in DerivedGraph
    /\ v2 \in DerivedGraph

(* Assumption about the cardinality of a bounded set construction *)
CardAssumption == CARD(BoundedSet(3)) = 3

(* Invariant checking the cardinality of the derived graph as computed by TLCEval *)
CardinalityInv ==
    CARD(TLCEval("DerivedGraph")) = 5

(* The complete specification *)
Spec == Init /\ [][Next]_<<v1,v2>>

(* Safety property: both type and cardinality invariants must hold forever *)
Safety == TypeInv /\ CardinalityInv

(* End of module *)