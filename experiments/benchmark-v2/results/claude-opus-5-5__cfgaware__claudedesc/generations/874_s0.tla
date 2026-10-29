---------------------------- MODULE APASpanTree ----------------------------
(***************************************************************************)
(* Apalache type annotations for the SpanTree specification. The          *)
(* definitions of SpanTree are given inline so that this module parses    *)
(* without depending on a separate file. They cover the distributed       *)
(* construction of a spanning tree that grows from Root.                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Nodes,
    \* @type: Set(Set(Str));
    Edges,
    \* @type: Str;
    Root,
    \* @type: Int;
    MaxCardinality

VARIABLES
    \* @type: Str -> Str;
    mom,
    \* @type: Str -> Int;
    dist

\* Concrete instantiation: a linear three-node graph n1 - n2 - n3, rooted at n1
NodesVal == {"n1", "n2", "n3"}
EdgesVal == {{"n1", "n2"}, {"n2", "n3"}}
RootVal  == "n1"

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

vars == <<mom, dist>>

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> Nat]
          /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == \E n \in Nodes :
          \E m \in Nbrs(n) :
             /\ dist[m] < 1 + dist[n]
             /\ \E d \in (dist[m] + 1) .. (dist[n] - 1) :
                    /\ dist' = [dist EXCEPT ![n] = d]
                    /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================