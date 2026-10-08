------------------------------- MODULE TinyStateSystem -------------------------------
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS Graph, Edges

VARIABLES x, y

(*--algorithm TinyStateSystem
variables x \in Edges, y \in Edges;
begin
    Init;
    while TRUE do
        with
            nx <- CHOOSE ex \in Edges: TRUE;
            ny <- CHOOSE ey \in Edges: TRUE;
        do
            x := nx;
            y := ny;
        end with;
    od;
end algorithm*)

Assume Cardinality({s \in SUBSET [1..2] -> Graph : Len(s) = 2}) = 4

Init == /\ x \in Edges
        /\ y \in Edges

Next ==
    \/ /\ x' \in Edges
       /\ y' \in Edges
    \/ /\ x' = x
       /\ y' = y

Spec ==
    Init /\ [][Next]_<<x, y>>

(* Type and membership invariants *)
TypeOK == /\ x \in Edges
           /\ y \in Edges

DerivedGraph == {e \in SUBSET Graph: Cardinality(e) = 2}
MembershipInvariant == \/ {x, y} \in DerivedGraph
                       \/ {y, x} \in DerivedGraph

(* TLCEval-specific cardinality check *)
CONSTANT TestGraph
TestGraphCardinalityCheck ==
    /\ TLC!TLCEval(Cardinality({s \in SUBSET [1..2] -> TestGraph : Len(s) = 2})) = 4

Invariant == TypeOK /\ MembershipInvariant /\ TestGraphCardinalityCheck

LiveFairness == WF_next(<<x, y>>)

SpecWithInvariants ==
    Spec /\ Inv(Invariant)
         /\ LiveFairness
=============================================================================