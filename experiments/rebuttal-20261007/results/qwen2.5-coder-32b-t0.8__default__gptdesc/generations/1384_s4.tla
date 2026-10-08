------------------------------- MODULE TinyStateSystem -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Graph, TestGraph

VARIABLES x, y

(*--algorithm TinyStateSystem
variables x \in SUBSET (Graph), y \in SUBSET (Graph)
begin
    Init:
        x := {};
        y := {}
end algorithm*)

Init == /\ x = {}
          /\ y = {}

Next == \/ /\ TLC!TLCEval(CHOICE e \in Graph : TRUE) \in TestGraph
              /\ x' = TLC!RandomElement(Graph)
              /\ y' = TLC!RandomElement(Graph)
          \/ /\ TLC!TLCEval(CHOICE e \in Graph : TRUE) \notin TestGraph
              /\ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y>> 

Assumption == Cardinality({s \in SUBSET Graph: TLC!TLCEval(CHOICE e \in s : TRUE) \in TestGraph}) = 5

TypeInvariant == /\ x \subseteq (Graph)
                 /\ y \subseteq (Graph)

DerivedTestGraphInvariant == /\ TLC!TLCEval(CHOICE e \in x : TRUE) \in TestGraph
                             /\ TLC!TLCEval(CHOICE e \in y : TRUE) \in TestGraph

Inv == TypeInvariant /\ DerivedTestGraphInvariant

Fairness == WF_next(x)

=============================================================================