MODULE GraphAgents

EXTENDS Naturals, Sequences, TLC

CONSTANTS
    NodeSet,
    FixedGraph,
    AuxGraph,
    F,
    ConstVal

VARIABLES e1, e2, seq

Init ==
  /\ e1 \in FixedGraph
  /\ e2 \in FixedGraph
  /\ seq \in { s \in Seq(NodeSet) :
        Len(s) <= 3
        /\ Sum([F[s[i]] | i \in 1..Len(s)]) = ConstVal }

Agent1Pick ==
  \E e \in FixedGraph :
    /\ e1' = e
    /\ UNCHANGED <<e2, seq>>

Agent2Pick ==
  \E e \in FixedGraph :
    /\ e2' = e
    /\ UNCHANGED <<e1, seq>>

SeqChange ==
  \E s \in { t \in Seq(NodeSet) :
        Len(t) <= 3
        /\ Sum([F[t[i]] | i \in 1..Len(t)]) = ConstVal } :
    /\ seq' = s
    /\ UNCHANGED <<e1, e2>>

Next == Agent1Pick \/ Agent2Pick \/ SeqChange

SafetyInvariant ==
  /\ e1 \in FixedGraph
  /\ e2 \in FixedGraph

CrossGraphInvariant ==
  /\ e1 \in AuxGraph
  /\ e2 \in AuxGraph

NumericInvariant ==
  Sum([F[seq[i]] | i \in 1..Len(seq)]) = ConstVal

Spec == Init /\ [][Next]_<<e1, e2, seq>>

Safety == [] SafetyInvariant
CrossGraph == [] CrossGraphInvariant
Numeric == [] NumericInvariant

THEOREM Spec => (Safety /\ CrossGraph /\ Numeric)