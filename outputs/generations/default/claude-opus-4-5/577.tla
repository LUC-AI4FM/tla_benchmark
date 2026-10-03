---------------------------- MODULE MCMultiNodeReadsAlt ----------------------------
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
    pendingReads,
    committedTxs

vars == <<ledgerBranches, history, nodeStates, pendingReads, committedTxs>>

-----------------------------------------------------------------------------
(* Type definitions and helpers *)

NullValue == CHOOSE v : v \notin Values

TxStatus == {"pending", "committed", "aborted"}

ReadOp == [type: {"read"}, txId: TxIds, key: Keys, node: Nodes]
WriteOp == [type: {"write"}, txId: TxIds, key: Keys, value: Values]
CommitOp == [type: {"commit"}, txId: TxIds]
ResponseOp == [type: {"response"}, txId: TxIds, key: Keys, value: Values \cup {NullValue}]

HistoryEntry == ReadOp \cup WriteOp \cup CommitOp \cup ResponseOp

-----------------------------------------------------------------------------
(* Base specification actions - MCNextMultiNodeReadsAction components *)

StartRead(txId, key, node) ==
    /\ txId \notin committedTxs
    /\ pendingReads' = pendingReads \cup {[txId |-> txId, key |-> key, node |-> node]}
    /\ history' = Append(history, [type |-> "read", txId |-> txId, key |-> key, node |-> node])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTxs>>

CompleteRead(txId, key, node, value) ==
    /\ [txId |-> txId, key |-> key, node |-> node] \in pendingReads
    /\ pendingReads' = pendingReads \ {[txId |-> txId, key |-> key, node |-> node]}
    /\ history' = Append(history, [type |-> "response", txId |-> txId, key |-> key, value |-> value])
    /\ UNCHANGED <<ledgerBranches, nodeStates, committedTxs>>

WriteKey(txId, key, value) ==
    /\ txId \notin committedTxs
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![txId] = 
                            [@ EXCEPT ![key] = value]]
    /\ history' = Append(history, [type |-> "write", txId |-> txId, key |-> key, value |-> value])
    /\ UNCHANGED <<nodeStates, pendingReads, committedTxs>>

CommitTx(txId) ==
    /\ txId \notin committedTxs
    /\ committedTxs' = committedTxs \cup {txId}
    /\ \A node \in Nodes:
        nodeStates' = [nodeStates EXCEPT ![node] = 
                        [k \in Keys |-> IF ledgerBranches[txId][k] # NullValue 
                                       THEN ledgerBranches[txId][k]
                                       ELSE nodeStates[node][k]]]
    /\ history' = Append(history, [type |-> "commit", txId |-> txId])
    /\ UNCHANGED <<ledgerBranches, pendingReads>>

MCNextMultiNodeReadsAction ==
    \/ \E txId \in TxIds, key \in Keys, node \in Nodes:
        StartRead(txId, key, node)
    \/ \E txId \in TxIds, key \in Keys, node \in Nodes, value \in Values \cup {NullValue}:
        CompleteRead(txId, key, node, value)
    \/ \E txId \in TxIds, key \in Keys, value \in Values:
        WriteKey(txId, key, value)
    \/ \E txId \in TxIds:
        CommitTx(txId)

-----------------------------------------------------------------------------
(* Alternative initial state - two transactions already committed *)

(* Helper to pick two distinct transaction IDs *)
ASSUME Cardinality(TxIds) >= 2
ASSUME Cardinality(Keys) >= 1
ASSUME Cardinality(Values) >= 2

Tx1 == CHOOSE t : t \in TxIds
Tx2 == CHOOSE t : t \in TxIds /\ t # Tx1

Key1 == CHOOSE k : k \in Keys

Val1 == CHOOSE v : v \in Values
Val2 == CHOOSE v : v \in Values /\ v # Val1

AltInit ==
    (* Two transactions are already committed *)
    /\ committedTxs = {Tx1, Tx2}
    
    (* Ledger branches reflect the committed writes *)
    /\ ledgerBranches = [txId \in TxIds |-> 
                            IF txId = Tx1 THEN [k \in Keys |-> IF k = Key1 THEN Val1 ELSE NullValue]
                            ELSE IF txId = Tx2 THEN [k \in Keys |-> IF k = Key1 THEN Val2 ELSE NullValue]
                            ELSE [k \in Keys |-> NullValue]]
    
    (* Node states reflect Tx2's value (committed after Tx1) *)
    /\ nodeStates = [node \in Nodes |-> [k \in Keys |-> IF k = Key1 THEN Val2 ELSE NullValue]]
    
    (* No pending reads initially *)
    /\ pendingReads = {}
    
    (* History shows the two transactions were written, responded to, and committed *)
    /\ history = <<
        [type |-> "write", txId |-> Tx1, key |-> Key1, value |-> Val1],
        [type |-> "commit", txId |-> Tx1],
        [type |-> "response", txId |-> Tx1, key |-> Key1, value |-> Val1],
        [type |-> "write", txId |-> Tx2, key |-> Key1, value |-> Val2],
        [type |-> "commit", txId |-> Tx2],
        [type |-> "response", txId |-> Tx2, key |-> Key1, value |-> Val2]
    >>

-----------------------------------------------------------------------------
(* Specification with alternative initial state *)

AltSpec == AltInit /\ [][MCNextMultiNodeReadsAction]_vars

-----------------------------------------------------------------------------
(* Safety Invariants *)

TypeInvariant ==
    /\ ledgerBranches \in [TxIds -> [Keys -> Values \cup {NullValue}]]
    /\ nodeStates \in [Nodes -> [Keys -> Values \cup {NullValue}]]
    /\ committedTxs \subseteq TxIds
    /\ pendingReads \subseteq [txId: TxIds, key: Keys, node: Nodes]

(* Committed transactions should have consistent state across nodes *)
ConsistencyInvariant ==
    \A n1, n2 \in Nodes: \A k \in Keys:
        nodeStates[n1][k] = nodeStates[n2][k]

(* History only contains valid entries *)
HistoryWellFormed ==
    \A i \in 1..Len(history):
        \/ history[i].type \in {"read", "write", "commit", "response"}

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Every pending read eventually completes *)
ReadEventuallyCompletes ==
    \A txId \in TxIds, key \in Keys, node \in Nodes:
        [txId |-> txId, key |-> key, node |-> node] \in pendingReads ~>
        [txId |-> txId, key |-> key, node |-> node] \notin pendingReads

=============================================================================