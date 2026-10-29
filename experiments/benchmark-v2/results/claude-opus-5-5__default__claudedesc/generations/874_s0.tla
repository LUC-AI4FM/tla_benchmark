---------------------------- MODULE APASpanTree ----------------------------
(***************************************************************************)
(* Apalache-annotated version of the SpanTree specification.  The original *)
(* SpanTree module is left untouched; this module declares the constants   *)
(* and variables with Apalache type annotations and reproduces the         *)
(* SpanTree behaviour so that the module is self-contained.                *)
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

vars == <<mom, dist>>

(***************************************************************************)
(* Concrete instantiation used for model checking: n1 -- n2 -- n3, root n1 *)
(***************************************************************************)
ConstInit ==
    /\ Nodes = {"n1", "n2", "n3"}
    /\ Edges = { {"n1", "n2"}, {"n2", "n3"} }
    /\ Root = "n1"
    /\ MaxCardinality = 4

ASSUME /\ Root \in Nodes
       /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
       /\ MaxCardinality \in Nat
       /\ MaxCardinality >= Cardinality(Nodes)

\* @type: Str => Set(Str);
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]

Init ==
    /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
    \E n \in Nodes :
      \E m \in Nbrs(n) :
        /\ dist[m] < 1 + dist[n]
        /\ \E d \in (dist[m] + 1)..(dist[n] - 1) :
              /\ dist' = [dist EXCEPT ![n] = d]
              /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties of the spanning tree construction.              *)
(***************************************************************************)
PostCondition ==
    \A n \in Nodes :
      \/ /\ n = Root
         /\ dist[n] = 0
         /\ mom[n] = n
      \/ /\ dist[n] = MaxCardinality
         /\ mom[n] = n
         /\ \A m \in Nbrs(n) : dist[m] = MaxCardinality
      \/ /\ dist[n] \in 1..(MaxCardinality - 1)
         /\ mom[n] \in Nbrs(n)
         /\ dist[n] = dist[mom[n]] + 1

Safety == []TypeOK

Liveness == <>[]PostCondition

THEOREM Spec => []TypeOK
=============================================================================