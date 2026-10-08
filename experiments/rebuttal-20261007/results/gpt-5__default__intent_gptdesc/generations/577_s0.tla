--------------------------- MODULE DistributedLedger ---------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Nodes, \* set of nodes
  Txns   \* universe of transaction identifiers

VARIABLES
  committed, \* sequence of systemwide committed transactions (no duplicates)
  proposed,  \* set of proposed transactions not yet decided
  rejected,  \* set of transactions decided not to commit
  visLen,    \* function Nodes -> Nat, length of local visible prefix per node
  readLen    \* function Nodes -> Nat, length of last-read observed prefix per node

\* Helper operators

DistinctSeq(s) ==
  \A i, j \in 1..Len(s) : (i # j) => (s[i] # s[j])

PrefixLen(s, k) == IF k <= Len(s) THEN k ELSE Len(s)

PrefixSet(s, k) ==
  { s[i] : i \in 1..PrefixLen(s, k) }

SetCommitted ==
  { committed[i] : i \in 1..Len(committed) }

VisibleSet(n) ==
  PrefixSet(committed, visLen[n])

ReadSet(n) ==
  PrefixSet(committed, readLen[n])

vars == << committed, proposed, rejected, visLen, readLen >>

\* Initial condition: an arbitrary already-committed history (possibly empty);
\* each node's visible branch is a prefix of it; reads return a prefix of the visible branch.

Init ==
  /\ committed \in Seq(Txns)
  /\ DistinctSeq(committed)
  /\ proposed \subseteq Txns
  /\ rejected \subseteq Txns
  /\ proposed \cap rejected = {}
  /\ proposed \cap SetCommitted = {}
  /\ visLen \in [Nodes -> Nat]
  /\ readLen \in [Nodes -> Nat]
  /\ \A n \in Nodes:
       /\ readLen[n] <= visLen[n]
       /\ visLen[n] <= Len(committed)

\* Actions

Propose(t) ==
  /\ t \in Txns
  /\ t \notin proposed \cup SetCommitted \cup rejected
  /\ proposed' = proposed \cup {t}
  /\ UNCHANGED << committed, rejected, visLen, readLen >>

Commit(t) ==
  /\ t \in proposed
  /\ t \notin SetCommitted
  /\ t \notin rejected
  /\ committed' = committed \o << t >>
  /\ proposed' = proposed \ {t}
  /\ UNCHANGED << rejected, visLen, readLen >>

Reject(t) ==
  /\ t \in proposed
  /\ t \notin SetCommitted
  /\ t \notin rejected
  /\ rejected' = rejected \cup {t}
  /\ proposed' = proposed \ {t}
  /\ UNCHANGED << committed, visLen, readLen >>

Propagate(n) ==
  /\ n \in Nodes
  /\ \E k \in Nat :
       /\ visLen[n] < k
       /\ k <= Len(committed)
       /\ visLen' = [visLen EXCEPT ![n] = k]
  /\ UNCHANGED << committed, proposed, rejected, readLen >>

Read(n) ==
  /\ n \in Nodes
  /\ \E r \in Nat :
       /\ readLen[n] <= r
       /\ r <= visLen[n]
       /\ readLen' = [readLen EXCEPT ![n] = r]
  /\ UNCHANGED << committed, proposed, rejected, visLen >>

Next ==
  \/ \E t \in Txns : Propose(t)
  \/ \E t \in Txns : Commit(t)
  \/ \E t \in Txns : Reject(t)
  \/ \E n \in Nodes: Propagate(n)
  \/ \E n \in Nodes: Read(n)

\* Fairness: eventual propagation of committed transactions to every node
Fairness ==
  \A n \in Nodes : WF_vars(Propagate(n))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

\* Safety invariants (state predicates)

TypeInv ==
  /\ committed \in Seq(Txns)
  /\ DistinctSeq(committed)
  /\ proposed \subseteq Txns
  /\ rejected \subseteq Txns
  /\ proposed \cap rejected = {}
  /\ proposed \cap SetCommitted = {}
  /\ visLen \in [Nodes -> Nat]
  /\ readLen \in [Nodes -> Nat]
  /\ \A n \in Nodes:
       /\ readLen[n] <= visLen[n]
       /\ visLen[n] <= Len(committed)

ReadsObserveCommitted ==
  \A n \in Nodes : ReadSet(n) \subseteq SetCommitted

ReadsWithinVisible ==
  \A n \in Nodes : ReadSet(n) \subseteq VisibleSet(n)

NoMissingPredecessors ==
  \A n \in Nodes :
    \A i, j \in 1..Len(committed) :
      (i < j /\ committed[j] \in ReadSet(n)) => committed[i] \in ReadSet(n)

Safety ==
  TypeInv /\ ReadsObserveCommitted /\ ReadsWithinVisible /\ NoMissingPredecessors

\* Temporal safety properties (monotonicity, durability)

MonotonicVisibility ==
  [](\A n \in Nodes : visLen[n] <= visLen'[n])

MonotonicReads ==
  [](\A n \in Nodes : ReadSet(n) \subseteq ReadSet(n)')

DurableCommits ==
  [](SetCommitted \subseteq SetCommitted')

\* Liveness: eventual visibility of any systemwide committed transaction at all nodes
EventualVisibility ==
  \A t \in Txns : [](t \in SetCommitted => <> (\A n \in Nodes : t \in VisibleSet(n)))

=============================================================================