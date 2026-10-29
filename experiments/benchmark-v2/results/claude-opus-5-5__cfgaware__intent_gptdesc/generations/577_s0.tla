```tla
xResponse
         /\ i /= j)
        => history[i].tx_id /= history[j].tx_id

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type \in RequestTypes
         /\ history[j].type \in RequestTypes
         /\ i /= j)
        => history[i].tx /= history[j].tx

UniqueSeqNumsCommittedInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].status = CommittedStatus
         /\ history[j].status = CommittedStatus
         /\ history[i].tx_id[2] = history[j].tx_id[2])
        => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].status = CommittedStatus
         /\ history[j].status = InvalidStatus)
        => ~(/\ history[j].tx_id[1] = history[i].tx_id[1]
             /\ history[j].tx_id[2] <= history[i].tx_id[2])

CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ IsCommitted(history[i].tx_id)
         /\ IsCommitted(history[j].tx_id)
         /\ history[i].tx_id[2] <= history[j].tx_id[2])
        => IsPrefix(history[i].observed, history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type \in ResponseTypes
         /\ IsInvalid(history[i].tx_id)
         /\ IsCommitted(history[j].tx_id))
        => ~InSeq(history[i].tx, history[j].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        history[i].type \in ResponseTypes =>
            \A a, b \in DOMAIN history[i].observed :
                history[i].observed[a] = history[i].observed[b] => a = b

-----------------------------------------------------------------------------
\* Liveness: committed tx ids eventually visible on the latest branch

EventualVisibilityProp ==
    \A t \in 1..HistoryLimit :
        [](( \E i \in DOMAIN history :
                /\ history[i].type = RwTxResponse
                /\ history[i].tx = t
                /\ IsCommitted(history[i].tx_id))
           ~> InSeq(t, LedgerBranchTxOnly(Last(ledgerBranches))))

=============================================================================
```