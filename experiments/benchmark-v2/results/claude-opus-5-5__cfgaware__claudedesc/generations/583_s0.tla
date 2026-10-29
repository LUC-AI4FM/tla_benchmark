---- MODULE MultiNode ----
EXTENDS SingleNode

\* Views (branches) of the ledger that preserve every committed entry.
\* Committed entries are those up to CommitSeqNum on the latest branch.
\* A leader change may only branch the ledger from such a view.
ViewWithAllCommitted ==
    { view \in DOMAIN ledgerBranches :
        /\ Len(ledgerBranches[view]) >= CommitSeqNum
        /\ \A i \in 1..CommitSeqNum :
            ledgerBranches[view][i] = ledgerBranches[Len(ledgerBranches)][i] }

\* Models a leader election. It picks a view that holds all committed entries.
\* It then truncates that branch at or after the commit point. The truncated
\* sequence is appended as a new branch, which starts a new view. This rolls
\* back uncommitted transactions and keeps committed state.
TruncateLedgerAction ==
    /\ \E view \in ViewWithAllCommitted :
        \E i \in (CommitSeqNum + 1)..(Len(ledgerBranches[view]) + 1) :
            ledgerBranches' =
                Append(ledgerBranches, SubSeq(ledgerBranches[view], 1, i - 1))
    /\ UNCHANGED <<CommittedTxIDs, history, CommitSeqNum>>

\* The view of the last committed transaction, or 0 if nothing is committed.
LastCommittedView ==
    IF Len(CommittedTxIDs) = 0 THEN 0
    ELSE CommittedTxIDs[Len(CommittedTxIDs)][1]

\* The current view, meaning the latest ledger branch.
CurrentView == Len(ledgerBranches)

\* The client receives an "invalid" status for a transaction it was told about.
StatusInvalidResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        \* Do not report the same transaction as invalid twice.
        /\ ~ \E j \in DOMAIN history :
                /\ history[j].type = TxStatusReceived
                /\ history[j].tx_id = history[i].tx_id
                /\ history[j].status = InvalidStatus
        /\ \/ \* Its seqnum was committed, but with a different view.
              \E k \in DOMAIN CommittedTxIDs :
                 /\ CommittedTxIDs[k][2] = history[i].tx_id[2]
                 /\ CommittedTxIDs[k][1] # history[i].tx_id[1]
           \/ \* The committed view is past the tx view, so it can never commit.
              /\ Len(CommittedTxIDs) > 0
              /\ LastCommittedView > history[i].tx_id[1]
           \/ \* The tx is in the current view but is still uncommitted.
              /\ history[i].tx_id[1] = CurrentView
              /\ ~ \E k \in DOMAIN CommittedTxIDs :
                    CommittedTxIDs[k] = history[i].tx_id
        /\ history' = Append(history,
                             [type   |-> TxStatusReceived,
                              tx_id  |-> history[i].tx_id,
                              status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, CommittedTxIDs, CommitSeqNum>>

\* Next-state relation: a single-node action, a ledger truncation,
\* or an invalid-status response.
NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

SpecMultiNode ==
    Init /\ [][NextMultiNodeAction]_<<ledgerBranches, history, CommitSeqNum, CommittedTxIDs>>

====