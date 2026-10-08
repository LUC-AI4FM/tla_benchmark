----------------------------- MODULE LedgerMultiNodeSpec -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  NODES,              \* Set of nodes
  TXN,                \* Set of transaction identifiers
  InitGCommitSeq,     \* Initial global committed sequence (a sequence over TXN, no duplicates)
  InitLocalSeq        \* Initial per-node local visible sequences: a function NODES -> Seq(TXN)

VARIABLES
  GCommitSeq,         \* Global committed transaction sequence (no duplicates)
  LocalSeq,           \* Per-node visible committed sequence; a prefix of GCommitSeq
  Proposed,           \* Set of proposed transactions (not yet globally committed)
  NodePending,        \* Per-node set of locally accepted (pending) transactions
  LastReadSet         \* Per-node last observed set returned by a read (monotonic, prefix-set of LocalSeq)

\* Helpers

SetSeq(s) == { s[i] : i \in 1..Len(s) }

NoDup(s) ==
  \A i, j \in 1..Len(s) : (i # j) => s[i] # s[j]

IsPrefix(s1, s2) ==
  \E k \in 0..Len(s2) : s1 = SubSeq(s2, 1, k)

PrefixSetOfLocal(n, S) ==
  \E k \in 0..Len(LocalSeq[n]) : S = SetSeq(SubSeq(LocalSeq[n], 1, k))

vars == << GCommitSeq, LocalSeq, Proposed, NodePending, LastReadSet >>

\* Initial states: allow some transactions already globally committed and visible as per-node prefixes.

Init ==
  /\ GCommitSeq = InitGCommitSeq
  /\ LocalSeq = InitLocalSeq
  /\ \A n \in NODES : IsPrefix(LocalSeq[n], GCommitSeq) /\ NoDup(LocalSeq[n])
  /\ NoDup(GCommitSeq)
  /\ Proposed = {}
  /\ NodePending = [n \in NODES |-> {}]
  /\ LastReadSet = [n \in NODES |-> SetSeq(LocalSeq[n])]

\* Actions

ProposeA(n, t) ==
  /\ n \in NODES
  /\ t \in TXN
  /\ t \notin SetSeq(GCommitSeq)
  /\ t \notin Proposed
  /\ NodePending' = [NodePending EXCEPT ![n] = @ \cup {t}]
  /\ Proposed' = Proposed \cup {t}
  /\ UNCHANGED << GCommitSeq, LocalSeq, LastReadSet >>

SystemCommitA(t) ==
  /\ t \in Proposed
  /\ t \notin SetSeq(GCommitSeq)
  /\ GCommitSeq' = Append(GCommitSeq, t)
  /\ Proposed' = Proposed \ {t}
  /\ NodePending' = [n \in NODES |-> NodePending[n] \ {t}]
  /\ UNCHANGED << LocalSeq, LastReadSet >>

AdvanceVisibleA(n) ==
  /\ n \in NODES
  /\ IsPrefix(LocalSeq[n], GCommitSeq)
  /\ Len(LocalSeq[n]) < Len(GCommitSeq)
  /\ LET old == LocalSeq[n] IN
       LocalSeq' = [LocalSeq EXCEPT ![n] = Append(old, GCommitSeq[Len(old)+1])]
  /\ UNCHANGED << GCommitSeq, Proposed, NodePending, LastReadSet >>

ReadA(n) ==
  /\ n \in NODES
  /\ \E k \in 0..Len(LocalSeq[n]) :
       /\ LastReadSet[n] \subseteq SetSeq(SubSeq(LocalSeq[n], 1, k))
       /\ LastReadSet' = [LastReadSet EXCEPT ![n] = SetSeq(SubSeq(LocalSeq[n], 1, k))]
  /\ UNCHANGED << GCommitSeq, LocalSeq, Proposed, NodePending >>

Next ==
  \/ \E n \in NODES, t \in TXN : ProposeA(n, t)
  \/ \E t \in TXN : SystemCommitA(t)
  \/ \E n \in NODES : AdvanceVisibleA(n)
  \/ \E n \in NODES : ReadA(n)

\* Fairness to ensure eventual visibility of globally committed transactions at all nodes.
Fairness ==
  \A n \in NODES : WF_vars(AdvanceVisibleA(n))

\* The complete specification
MCSpecMultiNodeReadsAlt ==
  Init /\ [][Next]_vars /\ Fairness

=============================================================================