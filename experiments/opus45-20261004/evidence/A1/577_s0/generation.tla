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

\* Helper operators
Nil == CHOOSE v : v \notin Values

\* Type definitions for history entries
ResponseEntry(txId, key, value) == [type |-> "response", txId |-> txId, key |-> key, value |-> value]
CommittedEntry(txId) == [type |-> "committed", txId |-> txId]

\* Base action definition (imported from base spec conceptually)
MCNextMultiNodeReadsAction ==
    \/ \E n \in Nodes, k \in Keys, txId \in TxIds :
        /\ pendingReads' = pendingReads \cup {[node |-> n, key |-> k, txId |-> txId]}
        /\ UNCHANGED <<ledgerBranches, history, nodeStates>>
    \/ \E pr \in pendingReads :
        /\ pendingReads' = pendingReads \ {pr}
        /\ \E v \in Values \cup {Nil} :
            /\ history' = Append(history, ResponseEntry(pr.txId, pr.key, v))
            /\ UNCHANGED <<ledgerBranches, nodeStates>>
    \/ \E txId \in TxIds :
        /\ history' = Append(history, CommittedEntry(txId))
        /\ UNCHANGED <<ledgerBranches, nodeStates, pendingReads>>
    \/ UNCHANGED vars

\* Alternative initial state with two transactions already committed
MCInitMultiNodeReadsAlt ==
    /\ ledgerBranches = [n \in Nodes |-> [k \in Keys |-> Nil]]
    /\ nodeStates = [n \in Nodes |-> "active"]
    /\ pendingReads = {}
    \* History pre-populated with two committed transactions
    /\ history = <<
        ResponseEntry("tx1", CHOOSE k \in Keys : TRUE, CHOOSE v \in Values : TRUE),
        CommittedEntry("tx1"),
        ResponseEntry("tx2", CHOOSE k \in Keys : TRUE, CHOOSE v \in Values : TRUE),
        CommittedEntry("tx2")
       >>

\* Temporal specification starting from alternative initial state
MCSpecMultiNodeReadsAlt ==
    MCInitMultiNodeReadsAlt /\ [][MCNextMultiNodeReadsAction]_vars

====