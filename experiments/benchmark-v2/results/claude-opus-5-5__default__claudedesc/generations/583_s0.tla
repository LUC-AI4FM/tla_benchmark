---- MODULE MultiNode ----
\* Multi-node CCF service model. It extends the single-node model with
\* consensus effects: leader election (ledger truncation into a new branch)
\* and transaction invalidation responses.

EXTENDS SingleNode

\* Views whose ledger branch keeps every committed entry. A new branch can
\* safely fork from these views after a leader change.
ViewWithAllCommitted ==
    { view \in DOMAIN ledgerBranches :
        /\ Len(ledgerBranches[view]) >= CommitSeqNum
        /\ \A i \in 1..CommitSeqNum :
            ledgerBranches[view][i] = ledgerBranches[Len(ledgerBranches)][i] }

\* View of the latest committed transaction (0 if nothing is committed yet)
CommittedView ==
    IF CommitSeqNum = 0
    THEN 0
    ELSE ledgerBranches[Len(ledgerBranches)][CommitSeqNum].view

\* Leader election. Some uncommitted transactions are rolled back and a new
\* view starts. The new branch keeps all committed entries, because the
\* truncation point is never before the commit point.
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E view \in ViewWithAllCommitted :
        \E i \in CommitSeqNum..Len(ledgerBranches[view]) :
            ledgerBranches' =
                Append(ledgerBranches, SubSeq(ledgerBranches[view], 1, i))
    /\ UNCHANGED <<history, CommitSeqNum>>

\* A transaction is reported Invalid if one of these holds:
\*  - its sequence number was committed in a different view,
\*  - the committed view is past the transaction's view, so it can never
\*    commit,
\*  - it belongs to the current view but is still uncommitted.
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id \notin CommittedTxIDs
        /\ \/ \E tx_id \in CommittedTxIDs :
                /\ tx_id[2] = history[i].tx_id[2]
                /\ tx_id[1] /= history[i].tx_id[1]
           \/ CommittedView > history[i].tx_id[1]
           \/ /\ history[i].tx_id[1] = Len(ledgerBranches)
              /\ history[i].tx_id[2] > CommitSeqNum
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, CommitSeqNum>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

SpecMultiNode ==
    Init /\ [][NextMultiNodeAction]_<<history, ledgerBranches, CommitSeqNum>>

====