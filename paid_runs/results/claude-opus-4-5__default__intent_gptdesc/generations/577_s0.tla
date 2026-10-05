---------------------------- MODULE DistributedLedger ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Nodes,          \* Set of node identifiers
    Transactions,   \* Set of transaction identifiers
    InitialCommits  \* Set of initially committed transactions

VARIABLES
    globalCommitted,    \* Set of globally committed transactions
    nodeVisible,        \* Function: node -> set of transactions visible at that node
    nodeObserved,       \* Function: node -> set of transactions observed by reads at that node
    pending,            \* Set of pending (proposed but not committed) transactions
    commitOrder,        \* Sequence representing the global commit order
    nodeCommitIndex     \* Function: node -> index into commitOrder that node has synced to

vars == <<globalCommitted, nodeVisible, nodeObserved, pending, commitOrder, nodeCommitIndex>>

\* Helper: Get the set of transactions in a prefix of commitOrder up to index i
CommitPrefix(i) == 
    IF i = 0 THEN {}
    ELSE {commitOrder[j] : j \in 1..i}

\* Type invariant
TypeOK ==
    /\ globalCommitted \subseteq Transactions
    /\ pending \subseteq Transactions
    /\ globalCommitted \cap pending = {}
    /\ nodeVisible \in [Nodes -> SUBSET Transactions]
    /\ nodeObserved \in [Nodes -> SUBSET Transactions]
    /\ commitOrder \in Seq(Transactions)
    /\ nodeCommitIndex \in [Nodes -> Nat]
    /\ \A n \in Nodes: nodeCommitIndex[n] <= Len(commitOrder)

\* Initial state: some transactions may already be committed
Init ==
    /\ globalCommitted = InitialCommits
    /\ pending = {}
    /\ commitOrder \in {s \in Seq(Transactions) : 
                         /\ Len(s) = Cardinality(InitialCommits)
                         /\ \A i \in 1..Len(s): s[i] \in InitialCommits
                         /\ \A t \in InitialCommits: \E i \in 1..Len(s): s[i] = t}
    /\ nodeCommitIndex \in [Nodes -> {i \in 0..Cardinality(InitialCommits) : TRUE}]
    /\ nodeVisible = [n \in Nodes |-> CommitPrefix(nodeCommitIndex[n])]
    /\ nodeObserved = [n \in Nodes |-> {}]

\* Propose a new transaction
Propose(t) ==
    /\ t \notin globalCommitted
    /\ t \notin pending
    /\ pending' = pending \cup {t}
    /\ UNCHANGED <<globalCommitted, nodeVisible, nodeObserved, commitOrder, nodeCommitIndex>>

\* Commit a pending transaction (makes it globally committed)
Commit(t) ==
    /\ t \in pending
    /\ pending' = pending \ {t}
    /\ globalCommitted' = globalCommitted \cup {t}
    /\ commitOrder' = Append(commitOrder, t)
    /\ UNCHANGED <<nodeVisible, nodeObserved, nodeCommitIndex>>

\* Node syncs to see more committed transactions (advances its view of commit order)
SyncNode(n) ==
    /\ nodeCommitIndex[n] < Len(commitOrder)
    /\ \E newIndex \in (nodeCommitIndex[n]+1)..Len(commitOrder):
        /\ nodeCommitIndex' = [nodeCommitIndex EXCEPT ![n] = newIndex]
        /\ nodeVisible' = [nodeVisible EXCEPT ![n] = CommitPrefix(newIndex)]
    /\ UNCHANGED <<globalCommitted, nodeObserved, pending, commitOrder>>

\* Read operation at a node: observes current visible transactions
\* The read updates nodeObserved to reflect what was seen (must be monotonic)
Read(n) ==
    /\ nodeObserved' = [nodeObserved EXCEPT ![n] = nodeObserved[n] \cup nodeVisible[n]]
    /\ UNCHANGED <<globalCommitted, nodeVisible, pending, commitOrder, nodeCommitIndex>>

\* Next state relation
Next ==
    \/ \E t \in Transactions: Propose(t)
    \/ \E t \in Transactions: Commit(t)
    \/ \E n \in Nodes: SyncNode(n)
    \/ \E n \in Nodes: Read(n)

\* Fairness: ensure progress
Fairness ==
    /\ \A t \in Transactions: WF_vars(Propose(t))
    /\ \A t \in Transactions: WF_vars(Commit(t))
    /\ \A n \in Nodes: WF_vars(SyncNode(n))
    /\ \A n \in Nodes: WF_vars(Read(n))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* --------------------------------------------------------------------------
\* SAFETY PROPERTIES
\* --------------------------------------------------------------------------

\* Once committed, a transaction stays committed (durability)
CommittedDurable ==
    [][globalCommitted \subseteq globalCommitted']_vars

\* Visible transactions at any node are a subset of globally committed
VisibleIsCommitted ==
    \A n \in Nodes: nodeVisible[n] \subseteq globalCommitted

\* Observed transactions are a subset of what was visible (and hence committed)
ObservedIsCommitted ==
    \A n \in Nodes: nodeObserved[n] \subseteq globalCommitted

\* Monotonic visibility: observed set never shrinks
MonotonicObserved ==
    [][\A n \in Nodes: nodeObserved[n] \subseteq nodeObserved'[n]]_vars

\* Monotonic visibility for node's visible set
MonotonicVisible ==
    [][\A n \in Nodes: nodeVisible[n] \subseteq nodeVisible'[n]]_vars

\* Prefix consistency: visible set at each node is a prefix of commit order
\* (no observing later commit while missing earlier predecessor)
PrefixConsistency ==
    \A n \in Nodes:
        \A i, j \in 1..Len(commitOrder):
            (i < j /\ commitOrder[j] \in nodeVisible[n]) => commitOrder[i] \in nodeVisible[n]

\* Observed prefix consistency
ObservedPrefixConsistency ==
    \A n \in Nodes:
        \A i, j \in 1..Len(commitOrder):
            (i < j /\ commitOrder[j] \in nodeObserved[n]) => commitOrder[i] \in nodeObserved[n]

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ VisibleIsCommitted
    /\ ObservedIsCommitted
    /\ PrefixConsistency
    /\ ObservedPrefixConsistency

\* --------------------------------------------------------------------------
\* LIVENESS PROPERTIES
\* --------------------------------------------------------------------------

\* Eventual visibility: if a transaction is globally committed, 
\* every node eventually makes it visible
EventualVisibility ==
    \A t \in Transactions:
        \A n \in Nodes:
            (t \in globalCommitted) ~> (t \in nodeVisible[n])

\* Eventual observation: if a transaction is globally committed,
\* reads at every node eventually observe it
EventualObservation ==
    \A t \in Transactions:
        \A n \in Nodes:
            (t \in globalCommitted) ~> (t \in nodeObserved[n])

\* All committed transactions are eventually visible everywhere
AllNodesEventuallySync ==
    \A n \in Nodes:
        [](globalCommitted # {} => <>(nodeVisible[n] = globalCommitted))

===============================================================================