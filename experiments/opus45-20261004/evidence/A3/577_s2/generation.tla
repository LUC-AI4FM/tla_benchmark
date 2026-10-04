---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,
    TxIds,
    Keys,
    Values

VARIABLES
    ledgerBranches,
    history,
    nodeStates,
    pendingRequests

vars == <<ledgerBranches, history, nodeStates, pendingRequests>>

-----------------------------------------------------------------------------
\* Base type definitions

NullValue == CHOOSE v : v \notin Values

TxStatuses == {"pending", "committed", "aborted"}

HistoryEntryTypes == {"request", "response", "committed"}

-----------------------------------------------------------------------------
\* Helper operators

EmptySeq == <<>>

-----------------------------------------------------------------------------
\* Base action definition (imported conceptually from base specification)

ReadKey(node, txId, key) ==
    /\ \E v \in Values \cup {NullValue}:
        /\ pendingRequests' = pendingRequests \cup {<<node, txId, key>>}
        /\ history' = Append(history, [type |-> "request", node |-> node, txId |-> txId, key |-> key])
        /\ UNCHANGED <<ledgerBranches, nodeStates>>

WriteKey(node, txId, key, value) ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![node] = Append(@, [txId |-> txId, key |-> key, value |-> value])]
    /\ history' = Append(history, [type |-> "request", node |-> node, txId |-> txId, key |-> key, value |-> value])
    /\ UNCHANGED <<nodeStates, pendingRequests>>

CommitTx(node, txId) ==
    /\ history' = Append(history, [type |-> "committed", node |-> node, txId |-> txId, status |-> "committed"])
    /\ nodeStates' = [nodeStates EXCEPT ![node][txId] = "committed"]
    /\ UNCHANGED <<ledgerBranches, pendingRequests>>

RespondToRead(node, txId, key, value) ==
    /\ <<node, txId, key>> \in pendingRequests
    /\ pendingRequests' = pendingRequests \ {<<node, txId, key>>}
    /\ history' = Append(history, [type |-> "response", node |-> node, txId |-> txId, key |-> key, value |-> value])
    /\ UNCHANGED <<ledgerBranches, nodeStates>>

MCNextMultiNodeReadsAction ==
    \/ \E node \in Nodes, txId \in TxIds, key \in Keys:
        ReadKey(node, txId, key)
    \/ \E node \in Nodes, txId \in TxIds, key \in Keys, value \in Values:
        WriteKey(node, txId, key, value)
    \/ \E node \in Nodes, txId \in TxIds:
        CommitTx(node, txId)
    \/ \E node \in Nodes, txId \in TxIds, key \in Keys, value \in Values \cup {NullValue}:
        RespondToRead(node, txId, key, value)

-----------------------------------------------------------------------------
\* Alternative Initial State
\* Initializes with two transactions already committed, with pre-populated
\* response and committed-status records in the history sequence

AltInit ==
    /\ Cardinality(Nodes) >= 1
    /\ Cardinality(TxIds) >= 2
    /\ Cardinality(Keys) >= 1
    /\ Cardinality(Values) >= 2
    /\ \E n1, n2 \in Nodes, tx1, tx2 \in TxIds, k1, k2 \in Keys, v1, v2 \in Values:
        /\ tx1 /= tx2
        \* Ledger branches contain entries from two committed transactions
        /\ ledgerBranches = [n \in Nodes |-> 
            IF n = n1 
            THEN <<[txId |-> tx1, key |-> k1, value |-> v1]>>
            ELSE IF n = n2 
            THEN <<[txId |-> tx2, key |-> k2, value |-> v2]>>
            ELSE <<>>]
        \* History shows responses and committed statuses for both transactions
        /\ history = <<
            [type |-> "response", node |-> n1, txId |-> tx1, key |-> k1, value |-> v1],
            [type |-> "committed", node |-> n1, txId |-> tx1, status |-> "committed"],
            [type |-> "response", node |-> n2, txId |-> tx2, key |-> k2, value |-> v2],
            [type |-> "committed", node |-> n2, txId |-> tx2, status |-> "committed"]
           >>
        \* Node states reflect committed transactions
        /\ nodeStates = [n \in Nodes |-> [t \in TxIds |-> 
            IF (n = n1 /\ t = tx1) \/ (n = n2 /\ t = tx2)
            THEN "committed"
            ELSE "pending"]]
        /\ pendingRequests = {}

-----------------------------------------------------------------------------
\* Temporal Specification using alternative initial state

Spec == AltInit /\ [][MCNextMultiNodeReadsAction]_vars

-----------------------------------------------------------------------------
\* Safety Invariants

TypeOK ==
    /\ ledgerBranches \in [Nodes -> Seq([txId: TxIds, key: Keys, value: Values])]
    /\ nodeStates \in [Nodes -> [TxIds -> TxStatuses]]
    /\ pendingRequests \subseteq (Nodes \times TxIds \times Keys)

\* A committed transaction's writes should be visible
CommittedWritesConsistent ==
    \A i \in 1..Len(history):
        history[i].type = "committed" /\ history[i].status = "committed" =>
            \E j \in 1..Len(ledgerBranches[history[i].node]):
                ledgerBranches[history[i].node][j].txId = history[i].txId

\* Invariant: all invariants combined
Inv == TypeOK /\ CommittedWritesConsistent

=============================================================================