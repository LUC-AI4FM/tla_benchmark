```tla
        \/  /\ history[i].type \in {RwTxResponse, RoTxResponse}
            /\ history[i].tx \in Txs
            /\ history[i].observed \in Seq(Txs)
            /\ history[i].tx_id \in TxIDs
        \/  /\ history[i].type = TxStatusReceived
            /\ history[i].tx_id \in TxIDs
            /\ history[i].status \in TxStatuses

LedgerTypeOK ==
    \A b \in DOMAIN ledgerBranches :
        \A k \in DOMAIN ledgerBranches[b] :
            /\ ledgerBranches[b][k].view \in Views
            /\ ledgerBranches[b][k].tx \in Txs

TypeOK == HistoryTypeOK /\ LedgerTypeOK

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..FirstBranch |-> <<>>]

----------------------------------------------------------------------------
\* Client actions (fresh requests also model retries after timeouts)

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* A leader of some view, possibly stale, executes a read-write transaction once
RwTxExecuteAction ==
    \E i \in RequestIdxs, b \in DOMAIN ledgerBranches :
        /\ history[i].type = RwTxRequest
        /\ history[i].tx \notin AllExecutedTxs
        /\ ledgerBranches' = [ledgerBranches EXCEPT
                                ![b] = Append(@, [view |-> b, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* The response to a read-write transaction is delivered at most once
RwTxResponseAction ==
    \E i \in RequestIdxs, b \in DOMAIN ledgerBranches :
        /\ history[i].type = RwTxRequest
        /\ ~Responded(history[i].tx)
        /\ \E k \in DOMAIN ledgerBranches[b] :
            /\ ledgerBranches[b][k].tx = history[i].tx
            /\ history' = Append(history,
                    [type     |-> RwTxResponse,
                     tx       |-> history[i].tx,
                     observed |-> Observed(ledgerBranches[b], k),
                     tx_id    |-> <<ledgerBranches[b][k].view, k>>])
        /\ UNCHANGED ledgerBranches

\* A read-only transaction is served by any node, possibly a lagging one,
\* from a consistent snapshot: a prefix of that node's ledger branch
RoTxResponseAction ==
    \E i \in RequestIdxs, b \in DOMAIN ledgerBranches :
        /\ history[i].type = RoTxRequest
        /\ ~Responded(history[i].tx)
        /\ \E k \in DOMAIN ledgerBranches[b] :
            history' = Append(history,
                    [type     |-> RoTxResponse,
                     tx       |-> history[i].tx,
                     observed |-> Observed(ledgerBranches[b], k),
                     tx_id    |-> <<ledgerBranches[b][k].view, k>>])
        /\ UNCHANGED ledgerBranches
```

```tla
\* A transaction ID is committed once it is in the latest leader's ledger
StatusCommittedAction ==
    \E i \in ResponseIdxs :
        LET id == history[i].tx_id IN
        /\ id \notin CommittedTxIDs \cup InvalidTxIDs
        /\ id[2] \in DOMAIN Latest
        /\ Latest[id[2]].view = id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> id, status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* A transaction ID is invalid once a later view has diverged from it.
\* This cannot be undone.
StatusInvalidAction ==
    \E i \in ResponseIdxs :
        LET id == history[i].tx_id IN
        /\ id \notin CommittedTxIDs \cup InvalidTxIDs
        /\ LatestView > id[1]
        /\ \/ id[2] > Len(Latest)
           \/ Latest[id[2]].view # id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> id, status |-> InvalidStatus])
        /\ UNCHANGED ledgerBranches

\* View change: a new leader starts a new branch. The branch is a prefix of
\* the latest branch that keeps every committed entry.
TruncateLedgerAction ==
    /\ LatestView < ViewLimit
    /\ \E k \in CommitSeqNum..Len(Latest) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, k))
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RoTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxResponseAction
    \/ StatusCommittedAction
    \/ StatusInvalidAction
    \/ TruncateLedgerAction

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ WF_vars(RwTxExecuteAction)
    /\ WF_vars(RwTxResponseAction)
    /\ WF_vars(RoTxResponseAction)
    /\ WF_vars(StatusCommittedAction)
    /\ WF_vars(StatusInvalidAction)

\* Liveness: every request is eventually answered under fair scheduling
EventuallyRespondedProp ==
    \A t \in 1..HistoryLimit :
        []((\E i \in RequestIdxs : history[i].tx = t) => <>Responded(t))

\* Model-checking specification with a bounded history
MCNext == Next /\ Len(history') <= HistoryLimit

MCSpecMultiNodeReads == Init /\ [][MCNext]_vars
```

```tla
----------------------------------------------------------------------------
\* Invariants

\* Every response follows a matching earlier request
AllReceivedIsFirstSentInv ==
    \A i \in ResponseIdxs :
        \E j \in RequestIdxs :
            /\ j < i
            /\ history[j].type = MatchingRequest(history[i].type)
            /\ history[j].tx = history[i].tx

\* A committed read-write tx is observed by every committed read-write tx
\* that has a higher sequence number
AllCommittedObservedInv ==
    \A i, j \in CommittedRwResponseIdxs :
        history[i].tx_id[2] < history[j].tx_id[2]
            => InSeq(history[i].tx, history[j].observed)

\* Reads return only values written by read-write txs that were requested
OnlyObserveSentRequestsInv ==
    \A i \in ResponseIdxs :
        \A k \in DOMAIN history[i].observed :
            \E j \in RequestIdxs :
                /\ j < i
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = history[i].observed[k]

\* Each tx gets at most one response
UniqueTxsInv ==
    \A i, j \in ResponseIdxs :
        history[i].tx = history[j].tx => i = j

\* Responses with the same tx ID observe the same state
SameObservationsInv ==
    \A i, j \in ResponseIdxs :
        history[i].tx_id = history[j].tx_id
            => history[i].observed = history[j].observed

\* Read-write txs have distinct tx IDs
UniqueTxIdsInv ==
    \A i, j \in RwResponseIdxs :
        history[i].tx_id = history[j].tx_id => i = j

\* Each tx is requested at most once
UniqueTxRequestsInv ==
    \A i, j \in RequestIdxs :
        history[i].tx = history[j].tx => i = j

\* Committed read-write txs have distinct sequence numbers,
\* so no committed update is lost or duplicated
UniqueSeqNumsCommittedInv ==
    \A i, j \in CommittedRwResponseIdxs :
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

\* No tx ID is both committed and invalid. Each tx ID receives at most one
\* status. Two different committed tx IDs never share a sequence number.
CommittedOrInvalidStrongInv ==
    /\ CommittedTxIDs \cap InvalidTxIDs = {}
    /\ \A i, j \in StatusIdxs :
        history[i].tx_id = history[j].tx_id => i = j
    /\ \A i, j \in CommittedStatusIdxs :
        history[i].tx_id[2] = history[j].tx_id[2]
            => history[i].tx_id = history[j].tx_id
```

```tla
\* Serializability: committed transactions (read-write and read-only) are
\* totally ordered by sequence number, and their observations grow by prefix.
\* This also gives read-only snapshot atomicity.
CommittedRwSerializableInv ==
    \A i, j \in CommittedResponseIdxs :
        history[i].tx_id[2] <= history[j].tx_id[2]
            => IsPrefix(history[i].observed, history[j].observed)

\* Write-atomicity: invalid writes are never observed by committed txs
InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwResponseIdxs :
        \A j \in CommittedResponseIdxs :
            ~InSeq(history[i].tx, history[j].observed)

\* No write appears twice in any observation
AtMostOnceObservedInv ==
    \A i \in ResponseIdxs :
        \A a, b \in DOMAIN history[i].observed :
            history[i].observed[a] = history[i].observed[b] => a = b

\* Real-time order: if a committed rw tx completes before another committed
\* rw tx is requested, the first one is ordered first
CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwResponseIdxs :
        (\E r \in RequestIdxs : r > i /\ history[r].tx = history[j].tx)
            => history[i].tx_id[2] < history[j].tx_id[2]

====
```