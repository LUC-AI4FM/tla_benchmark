------------------------------- MODULE GraphSystem -------------------------------

EXTENDS Sequences, TLC, FiniteSets

CONSTANTS Vertices, Edges
ASSUME Vertices \in Nat
ASSUME Edges \subseteq (Vertices \cross Vertices)
ASSUME Cardinality({s \in Seq(Edges) : Len(s) = 2}) = 4

VARIABLES x, y

Init == /\ x \in Edges
        /\ y \in Edges

Next == \/ /\ x' \in Edges
            /\ y' = y
          \/ /\ x' = x
            /\ y' \in Edges

Spec == Init /\ [][Next]_<<x, y>>

INVARIANT Cardinality({s \in Seq(Edges) : Len(s) = 2}) = TLCEval(Cardinality({s \in Seq(Edges) : Len(s) = 2}))
INVARIENT x \in Edges
INVARIENT y \in Edges
INVARIENT \/ x = y
           \/ <<x, y>> \in Edges

LIVENESS == <>[]<>(x' \notin {x})

=============================================================================