---- MODULE spec ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,
    Keys,
    Values,
    TxIds,
    MaxTransactions

VARIABLES
    ledgerBranches,
    history,
    nodeStates,
    pendingReads

vars == <<ledgerBranches, history, nodeStates, pendingReads>>

\* Base definitions for the multi-node reads model

NullValue == CHOOSE v : v \notin Values

TypeOK ==
    /\ ledgerBranches \in [Nodes -> [Keys -> Values \cup {NullValue}]]
    /\ history \in Seq([type: {"read", "write", "commit", "response"}, 
                        txId: TxIds, 
                        key: Keys \cup {NullValue}, 
                        value: Values \cup {NullValue},
                        node: Nodes \cup {NullValue},
                        committed: BOOLEAN])
    /\ nodeStates \in [Nodes -> [active: BOOLEAN, lastTx: TxIds \cup {NullValue}]]
    /\ pendingReads \in SUBSET [txId: TxIds, key: Keys, node: Nodes]

\* Helper to pick an arbitrary element
PickNode == CHOOSE n \in Nodes : TRUE
PickKey == CHOOSE k \in Keys : TRUE
PickValue == CHOOSE v \in Values : TRUE
PickTxId1 == CHOOSE t \in TxIds : TRUE
PickTxId2 == CHOOSE t \in TxIds : t /= PickTxId1

\* Standard initial state
MCInitMultiNodeReads ==
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> NullValue]]
    /\ history = <<>>
    /\ nodeStates = [n \in Nodes |-> [active |-> TRUE, lastTx |-> NullValue]]
    /\ pendingReads = {}

\* Alternative initial state with two transactions already committed
MCInitMultiNodeReadsAlt ==
    LET 
        node1 == PickNode
        key1 == PickKey
        value1 == PickValue
        txId1 == PickTxId1
        txId2 == PickTxId2
    IN
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> IF k = key1 THEN value1 ELSE NullValue]]
    /\ history = <<
        [type |-> "write", txId |-> txId1, key |-> key1, value |-> value1, node |-> node1, committed |-> TRUE],
        [type |-> "commit", txId |-> txId1, key |-> NullValue, value |-> NullValue, node |-> node1, committed |-> TRUE],
        [type |-> "response", txId |-> txId1, key |-> NullValue, value |-> NullValue, node |-> node1, committed |-> TRUE],
        [type |-> "write", txId |-> txId2, key |-> key1, value |-> value1, node |-> node1, committed |-> TRUE],
        [type |-> "commit", txId |-> txId2, key |-> NullValue, value |-> NullValue, node |-> node1, committed |-> TRUE],
        [type |-> "response", txId |-> txId2, key |-> NullValue, value |-> NullValue, node |-> node1, committed |-> TRUE]
    >>
    /\ nodeStates = [n \in Nodes |-> [active |-> TRUE, lastTx |-> IF n = node1 THEN txId2 ELSE NullValue]]
    /\ pendingReads = {}

\* Read action
ReadAction ==
    \E n \in Nodes, k \in Keys, t \in TxIds :
        /\ nodeStates[n].active
        /\ Len(history) < MaxTransactions
        /\ pendingReads' = pendingReads \cup {[txId |-> t, key |-> k, node |-> n]}
        /\ history' = Append(history, [type |-> "read", txId |-> t, key |-> k, 
                                        value |-> ledgerBranches[n][k], node |-> n, committed |-> FALSE])
        /\ UNCHANGED <<ledgerBranches, nodeStates>>

\* Write action
WriteAction ==
    \E n \in Nodes, k \in Keys, v \in Values, t \in TxIds :
        /\ nodeStates[n].active
        /\ Len(history) < MaxTransactions
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![n][k] = v]
        /\ history' = Append(history, [type |-> "write", txId |-> t, key |-> k, 
                                        value |-> v, node |-> n, committed |-> FALSE])
        /\ UNCHANGED <<nodeStates, pendingReads>>

\* Commit action
CommitAction ==
    \E n \in Nodes, t \in TxIds :
        /\ nodeStates[n].active
        /\ Len(history) < MaxTransactions
        /\ history' = Append(history, [type |-> "commit", txId |-> t, key |-> NullValue, 
                                        value |-> NullValue, node |-> n, committed |-> TRUE])
        /\ nodeStates' = [nodeStates EXCEPT ![n].lastTx = t]
        /\ UNCHANGED <<ledgerBranches, pendingReads>>

\* Response action
ResponseAction ==
    \E pr \in pendingReads :
        /\ Len(history) < MaxTransactions
        /\ history' = Append(history, [type |-> "response", txId |-> pr.txId, key |-> pr.key, 
                                        value |-> ledgerBranches[pr.node][pr.key], 
                                        node |-> pr.node, committed |-> TRUE])
        /\ pendingReads' = pendingReads \ {pr}
        /\ UNCHANGED <<ledgerBranches, nodeStates>>

\* Combined next action for multi-node reads
MCNextMultiNodeReadsAction ==
    \/ ReadAction
    \/ WriteAction
    \/ CommitAction
    \/ ResponseAction

\* Standard specification
MCSpecMultiNodeReads ==
    /\ MCInitMultiNodeReads
    /\ [][MCNextMultiNodeReadsAction]_vars

\* Alternative specification starting from the state with two committed transactions
MCSpecMultiNodeReadsAlt ==
    /\ MCInitMultiNodeReadsAlt
    /\ [][MCNextMultiNodeReadsAction]_vars

====