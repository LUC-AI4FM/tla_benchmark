------------------------------- MODULE TinyStateSystem -------------------------------
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS Graph, TestGraph

VARIABLES x, y

Init == /\ x \in Graph
        /\ y \in Graph

Next == \/ /\ x' = RandomElement(Graph)
            /\ y' = RandomElement(Graph)
        \/ /\ x' = y
           /\ y' = x

Spec == Init /\ [][Next]_<<x, y>>

(*--algorithm TinyStateSystem
variables x, y;
begin
    Init;
    while TRUE do
        either
            x := RandomElement(Graph);
            y := RandomElement(Graph);
        or
            x := y;
            y := x;
        end either;
    od;
end algorithm*)

Assumption == Cardinality({seq \in Seq(Graph) : Len(seq) = 2}) = Cardinality(Graph) * Cardinality(Graph)

TypeInvariant == /\ x \in Graph
                 /\ y \in Graph

GraphMembershipInvariant == /\ {x, y} \subseteq TestGraph
                          /\ {y, x} \subseteq TestGraph

CardinalityCheck == TLCEval(Cardinality({seq \in Seq(Graph) : Len(seq) = 2})) = Cardinality(Graph) * Cardinality(Graph)

Invariants == TypeInvariant /\ GraphMembershipInvariant /\ CardinalityCheck

SpecWithInvariants == Spec /\ WF_next(<<x, y>>) /\ Invariants
================================================================================