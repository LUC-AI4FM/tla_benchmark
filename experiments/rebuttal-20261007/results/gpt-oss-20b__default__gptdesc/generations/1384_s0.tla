MODULE GraphSpec
EXTENDS Naturals, Sequences, TLC

CONSTANTS G, N, TestNodes

VARIABLE v1, v2

(* Helper operator: BoundedSeq(S, n) returns all sequences over S with length <= n *)
BoundedSeq == [S, n |-> { s \in Seq(S) : Len(s) <= n } ]

(* Derived test graph: edges where source node is in TestNodes *)
DerivedGraph == { e \in G : e[1] \in TestNodes }

(* TLCEval and RandomElement are provided by TLC; we declare them as operators for type-checking *)
TLCEval(e) == e
RandomElement(S) == CHOOSE x \in S : TRUE

AssumeCardinality ==
  # (BoundedSeq[G, N]) = 2^N * (#G)^N

Invariant ==
  /\ v1 \in G
  /\ v2 \in G
  /\ v1 \in DerivedGraph
  /\ v2 \in DerivedGraph
  /\ # (BoundedSeq[G, N]) = TLCEval( 2^N * (#G)^N )

Init == 
  /\ v1 \in G
  /\ v2 \in G

Next ==
  \/ /\ v1' \in G
     /\ v2' = v2
  \/ /\ v1' = v1
     /\ v2' \in G

Spec == Init /\ [][Next]_<<v1, v2>> /\ []Invariant

\* The TLCEval operator forces evaluation of the cardinality expression in the current state.
\* Caching of BoundedSeq may affect the invariant if not recomputed each step.