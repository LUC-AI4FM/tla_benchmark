---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,
    Keys,
    Values,
    TxnIds,
    MaxTransactions

VARIABLES
    ledgerBranches,
    history,
    nodeStates,
    pendingReads,
    committedTxns

vars == <<ledgerBranches, history, nodeStates, pendingReads, committedTxns>>

-----------------------------------------------------------------------------
(* Type definitions and helpers *)

NullValue == CHOOSE v : v \notin Values

TxnStatus == {"pending", "committed", "aborted"}

HistoryEntry == [type: {"request", "response", "commit", "abort"}, 
                 txnId: TxnIds, 
                 key: Keys \cup {""}, 
                 value: Values \cup {NullValue}]

-----------------------------------------------------------------------------
(* Base specification actions - MCNextMultiNodeReadsAction *)

ReadKey(node, txnId, key) ==
    /\ nodeStates[node].activeTxn = txnId
    /\ txnId \notin committedTxns
    /\ pendingReads' = pendingReads \cup {[node |-> node, txnId |-> txnId, key |-> key]}
    /\ history' = Append(history, [type |-> "request", txnId |-> txnId, key |-> key, value |-> NullValue])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTxns>>

CompleteRead(node, txnId, key, value) ==
    /\ [node |-> node, txnId |-> txnId, key |-> key] \in pendingReads
    /\ pendingReads' = pendingReads \ {[node |-> node, txnId |-> txnId, key |-> key]}
    /\ history' = Append(history, [type |-> "response", txnId |-> txnId, key |-> key, value |-> value])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTxns>>

CommitTxn(txnId) ==
    /\ txnId \notin committedTxns
    /\ \A r \in pendingReads : r.txnId # txnId
    /\ committedTxns' = committedTxns \cup {txnId}
    /\ history' = Append(history, [type |-> "commit", txnId |-> txnId, key |-> "", value |-> NullValue])
    /\ UNCHANGED <<ledgerBranches, nodeStates, pendingReads>>

StartTxn(node, txnId) ==
    /\ nodeStates[node].activeTxn = NullValue
    /\ txnId \notin committedTxns
    /\ \A n \in Nodes : nodeStates[n].activeTxn # txnId
    /\ nodeStates' = [nodeStates EXCEPT ![node].activeTxn = txnId]
    /\ UNCHANGED <<ledgerBranches, history, pendingReads, committedTxns>>

EndTxn(node) ==
    /\ nodeStates[node].activeTxn # NullValue
    /\ nodeStates' = [nodeStates EXCEPT ![node].activeTxn = NullValue]
    /\ UNCHANGED <<ledgerBranches, history, pendingReads, committedTxns>>

UpdateLedger(node, key, value) ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![node][key] = value]
    /\ UNCHANGED <<history, nodeStates, pendingReads, committedTxns>>

MCNextMultiNodeReadsAction ==
    \/ \E node \in Nodes, txnId \in TxnIds, key \in Keys :
        ReadKey(node, txnId, key)
    \/ \E node \in Nodes, txnId \in TxnIds, key \in Keys, value \in Values :
        CompleteRead(node, txnId, key, value)
    \/ \E txnId \in TxnIds :
        CommitTxn(txnId)
    \/ \E node \in Nodes, txnId \in TxnIds :
        StartTxn(node, txnId)
    \/ \E node \in Nodes :
        EndTxn(node)
    \/ \E node \in Nodes, key \in Keys, value \in Values :
        UpdateLedger(node, key, value)

-----------------------------------------------------------------------------
(* Alternative Initial State - Two transactions already committed *)

ASSUME Cardinality(TxnIds) >= 2
ASSUME Cardinality(Keys) >= 1
ASSUME Cardinality(Values) >= 2

Txn1 == CHOOSE t1 \in TxnIds : TRUE
Txn2 == CHOOSE t2 \in TxnIds : t2 # Txn1

Key1 == CHOOSE k \in Keys : TRUE

Val1 == CHOOSE v1 \in Values : TRUE
Val2 == CHOOSE v2 \in Values : v2 # Val1

InitAlt ==
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> Val2]]
    /\ history = <<
        [type |-> "request", txnId |-> Txn1, key |-> Key1, value |-> NullValue],
        [type |-> "response", txnId |-> Txn1, key |-> Key1, value |-> Val1],
        [type |-> "commit", txnId |-> Txn1, key |-> "", value |-> NullValue],
        [type |-> "request", txnId |-> Txn2, key |-> Key1, value |-> NullValue],
        [type |-> "response", txnId |-> Txn2, key |-> Key1, value |-> Val2],
        [type |-> "commit", txnId |-> Txn2, key |-> "", value |-> NullValue]
       >>
    /\ nodeStates = [n \in Nodes |-> [activeTxn |-> NullValue]]
    /\ pendingReads = {}
    /\ committedTxns = {Txn1, Txn2}

-----------------------------------------------------------------------------
(* Temporal Specification *)

SpecAlt == InitAlt /\ [][MCNextMultiNodeReadsAction]_vars

-----------------------------------------------------------------------------
(* Safety Invariants *)

TypeInvariant ==
    /\ ledgerBranches \in [Nodes -> [Keys -> Values]]
    /\ history \in Seq(HistoryEntry)
    /\ nodeStates \in [Nodes -> [activeTxn: TxnIds \cup {NullValue}]]
    /\ pendingReads \subseteq [node: Nodes, txnId: TxnIds, key: Keys]
    /\ committedTxns \subseteq TxnIds

CommittedTxnsMonotonic ==
    [][committedTxns \subseteq committedTxns']_vars

HistoryMonotonic ==
    [][Len(history) <= Len(history')]_vars

NoDoubleCommit ==
    \A i, j \in 1..Len(history) :
        (i # j /\ history[i].type = "commit" /\ history[j].type = "commit")
        => history[i].txnId # history[j].txnId

-----------------------------------------------------------------------------
(* Liveness Properties *)

EventuallyMoreCommits ==
    <>(Cardinality(committedTxns) > 2)

=============================================================================