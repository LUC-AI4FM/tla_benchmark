---------------------------- MODULE MCSpecMultiNodeReadsAlt ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* Set of node identifiers
    Transactions,   \* Set of transaction identifiers
    MaxCommits      \* Maximum number of commits to bound model checking

VARIABLES
    committedLog,       \* Global sequence of committed transactions (total order)
    nodeVisible,        \* nodeVisible[n] = set of transactions visible at node n
    pendingTxns,        \* Set of transactions proposed but not yet committed
    readHistory,        \* readHistory[n] = sequence of read results at node n
    commitCount         \* Counter to bound commits for model checking

vars == <<committedLog, nodeVisible, pendingTxns, readHistory, commitCount>>

-----------------------------------------------------------------------------
(* Type invariants and helpers *)

TypeOK ==
    /\ committedLog \in Seq(Transactions)
    /\ \A n \in Nodes: nodeVisible[n] \subseteq Transactions
    /\ pendingTxns \subseteq Transactions
    /\ \A n \in Nodes: readHistory[n] \in Seq(SUBSET Transactions)
    /\ commitCount \in Nat

\* Set of transactions in the committed log
CommittedSet == {committedLog[i] : i \in 1..Len(committedLog)}

\* Prefix of committed log up to index i as a set
PrefixSet(i) == {committedLog[j] : j \in 1..i}

\* Check if a set S is a valid prefix of the committed log
IsValidPrefix(S) ==
    \E i \in 0..Len(committedLog):
        S = IF i = 0 THEN {} ELSE PrefixSet(i)

-----------------------------------------------------------------------------
(* Initial state - allows some transactions to be already committed *)

Init ==
    /\ committedLog \in Seq(Transactions)  \* May start with some committed txns
    /\ Len(committedLog) <= MaxCommits
    /\ \A i, j \in 1..Len(committedLog): i # j => committedLog[i] # committedLog[j]
    /\ \A n \in Nodes: 
        \* Each node sees some prefix of committed transactions
        \E k \in 0..Len(committedLog):
            nodeVisible[n] = IF k = 0 THEN {} ELSE PrefixSet(k)
    /\ pendingTxns = Transactions \ CommittedSet
    /\ \A n \in Nodes: readHistory[n] = <<>>
    /\ commitCount = Len(committedLog)

-----------------------------------------------------------------------------
(* Actions *)

\* A node proposes a new transaction (moves from pending to proposed state)
\* For simplicity, transactions go directly from pending to being committed
ProposeTransaction(t) ==
    /\ t \in pendingTxns
    /\ UNCHANGED vars

\* Commit a pending transaction - adds to global committed log
CommitTransaction(t) ==
    /\ t \in pendingTxns
    /\ commitCount < MaxCommits
    /\ committedLog' = Append(committedLog, t)
    /\ pendingTxns' = pendingTxns \ {t}
    /\ commitCount' = commitCount + 1
    /\ UNCHANGED <<nodeVisible, readHistory>>

\* A node learns about committed transactions (propagation)
\* Node visibility must grow as a prefix of the committed log
PropagateToNode(n) ==
    /\ \E k \in 0..Len(committedLog):
        LET newVisible == IF k = 0 THEN {} ELSE PrefixSet(k)
        IN
            /\ nodeVisible[n] \subseteq newVisible  \* Can only grow (monotonic)
            /\ nodeVisible[n] # newVisible          \* Must actually change
            /\ nodeVisible'= [nodeVisible EXCEPT ![n] = newVisible]
    /\ UNCHANGED <<committedLog, pendingTxns, readHistory, commitCount>>

\* A node performs a read operation - returns current visible set
\* The read result is recorded in history for property checking
ReadAtNode(n) ==
    /\ readHistory' = [readHistory EXCEPT ![n] = Append(readHistory[n], nodeVisible[n])]
    /\ UNCHANGED <<committedLog, nodeVisible, pendingTxns, commitCount>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E t \in Transactions: CommitTransaction(t)
    \/ \E n \in Nodes: PropagateToNode(n)
    \/ \E n \in Nodes: ReadAtNode(n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Fairness conditions for liveness *)

Fairness ==
    /\ \A n \in Nodes: WF_vars(PropagateToNode(n))
    /\ \A n \in Nodes: WF_vars(ReadAtNode(n))

FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Once committed, a transaction is never uncommitted
CommitDurability ==
    [][
        \A t \in Transactions:
            t \in CommittedSet => t \in CommittedSet'
    ]_vars

\* Monotonic visibility - reads at a node never see fewer transactions
MonotonicVisibility ==
    \A n \in Nodes:
        \A i \in 1..Len(readHistory[n]):
            \A j \in 1..Len(readHistory[n]):
                i <= j => readHistory[n][i] \subseteq readHistory[n][j]

\* Node visibility only grows (monotonic)
MonotonicNodeVisibility ==
    [][\A n \in Nodes: nodeVisible[n] \subseteq nodeVisible'[n]]_vars

\* All visible sets at nodes are valid prefixes of committed log
ConsistentPrefixReads ==
    \A n \in Nodes: IsValidPrefix(nodeVisible[n])

\* Read history contains only valid prefixes
ReadHistoryConsistent ==
    \A n \in Nodes:
        \A i \in 1..Len(readHistory[n]):
            IsValidPrefix(readHistory[n][i])

\* Safety invariant combining key properties
SafetyInvariant ==
    /\ TypeOK
    /\ ConsistentPrefixReads
    /\ ReadHistoryConsistent
    /\ MonotonicVisibility

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Eventually all committed transactions become visible at all nodes
EventualVisibility ==
    \A t \in Transactions:
        \A n \in Nodes:
            (t \in CommittedSet) ~> (t \in nodeVisible[n])

\* All nodes eventually see all committed transactions
EventualConsistency ==
    <>(\A n \in Nodes: nodeVisible[n] = CommittedSet)

-----------------------------------------------------------------------------
(* Main specification for model checking *)

MCSpecMultiNodeReadsAlt == FairSpec

=============================================================================