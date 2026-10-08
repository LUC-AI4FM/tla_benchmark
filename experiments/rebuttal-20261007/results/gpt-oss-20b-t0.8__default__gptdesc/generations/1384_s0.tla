--------------------------- MODULE GraphSpec ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,
    EdgeSet,            \* subset of [Node × Node] where Node ⊆ Nodes
    SomeNode,
    AnotherNode

VARIABLES a, b

(* Helper operators *)

BoundedSeq(n) == { seq \in Seq(Nodes) : Len(seq) <= n }

RandomElement(S) ==
    CHOOSE x \in S : TRUE

TLCEval(e) == e   \* identity to force evaluation in TLC context

(* Derived graph sets *)

TestGraph == TLCEval( { e \in EdgeSet : e[1] = SomeNode } )

OtherGraph == TLCEval( { e \in EdgeSet : e[2] = AnotherNode } )

(* Assumption about cardinality of nested bounded sequence *)
AssumeCardinality ==
    Len(TestGraph) = 3

(* Initial state *)

Init ==
    /\ a \in EdgeSet
    /\ b \in EdgeSet
    /\ AssumeCardinality

(* Next-state relation *)

Next ==
    \/ a' = RandomElement(EdgeSet)
       /\ b' = b
    \/ a' = a
       /\ b' = RandomElement(EdgeSet)

(* Invariants *)

TypeInv == a \in EdgeSet /\ b \in EdgeSet

GraphMembership == a \in TestGraph /\ b \in TestGraph

CardinalityInvariant == Len(TestGraph) = 3

Inv ==
    TypeInv /\ GraphMembership /\ CardinalityInvariant

(* Specification *)

Spec == Init /\ [][Next]_<<a,b>> /\ Inv
=============================================================================