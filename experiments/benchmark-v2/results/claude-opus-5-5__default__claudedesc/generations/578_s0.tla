---------------------------- MODULE MCMultiNodeReads ----------------------------
\* Bounded model-checking specification of a multi-node distributed system that
\* supports both read-write and read-only transactions.
\* It is self-contained here so that it parses on its own. It inlines the
\* behaviour of MCSingleNodeReads (read-only transactions) and MCMultiNode
\* (multi-node read-write transactions with views, branches and commit).
\* Deadlock checking is meant to be disabled (CHECK_DEADLOCK FALSE).

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus

\* Model bounds
HistoryLimit == 6
ViewLimit    == 3
FirstBranch  == 1

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* sequence (indexed by view) of ledger branches
    commitSeqNum     \* highest committed sequence number

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
\* Helpers

CurrentView == Len(ledgerBranches)
Latest      == ledgerBranches[CurrentView]

IsResponse(i) == history[i].type \in {RwTxResponse, RoTxResponse}

InLedger(t) ==
    \E b \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[b] : ledgerBranches[b][k].tx = t

Responded(t, ty) ==
    \E i \in DOMAIN history : history[i].type = ty /\ history[i].tx = t

HasStatus(tid) ==
    \E i \in DOMAIN history :
        history[i].type = TxStatusReceived /\ history[i].tx_id = tid

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in 1..FirstBranch |-> <<>>]
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
\* Multi-node (read-write) actions

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RwTxRequest
         /\ ~InLedger(history[i].tx)
         /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E j \in DOMAIN Latest :
         /\ ~Responded(Latest[j].tx, RwTxResponse)
         /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> Latest[j].tx,
                 observed |-> [k \in 1..j |-> Latest[k].tx],
                 tx_id    |-> <<Latest[j].view, j>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in commitSeqNum..Len(Latest) :
         ledgerBranches' = Append(ledgerBranches, SubSeq(Latest, 1, i))
    /\ UNCHANGED <<history, commitSeqNum>>

CommitAction ==
    /\ \E i \in (commitSeqNum + 1)..Len(Latest) : commitSeqNum' = i
    /\ UNCHANGED <<history, ledgerBranches>>

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
         /\ IsResponse(i)
         /\ ~HasStatus(history[i].tx_id)
         /\ history[i].tx_id[2] <= commitSeqNum
         /\ Latest[history[i].tx_id[2]].view = history[i].tx_id[1]
         /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
         /\ IsResponse(i)
         /\ ~HasStatus(history[i].tx_id)
         /\ history[i].tx_id[2] <= commitSeqNum
         /\ Latest[history[i].tx_id[2]].view # history[i].tx_id[1]
         /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

MultiNodeNext ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ TruncateLedgerAction
    \/ CommitAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

-----------------------------------------------------------------------------
\* Read-only actions

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ Len(Latest) > 0
    /\ \E i \in DOMAIN history :
         /\ history[i].type = RoTxRequest
         /\ ~Responded(history[i].tx, RoTxResponse)
         /\ history' = Append(history,
                [type     |-> RoTxResponse,
                 tx       |-> history[i].tx,
                 observed |-> [k \in 1..Len(Latest) |-> Latest[k].tx],
                 tx_id    |-> <<Latest[Len(Latest)].view, Len(Latest)>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
Next ==
    \/ MultiNodeNext
    \/ RoTxRequestAction
    \/ RoTxResponseAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Derived sets for invariants

RequestIdx    == {i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}}
RwResponseIdx == {i \in DOMAIN history : history[i].type = RwTxResponse}
ResponseIdx   == {i \in DOMAIN history : IsResponse(i)}
StatusIdx     == {i \in DOMAIN history : history[i].type = TxStatusReceived}

CommittedTxIds ==
    {history[i].tx_id : i \in {k \in StatusIdx : history[k].status = CommittedStatus}}
InvalidTxIds ==
    {history[i].tx_id : i \in {k \in StatusIdx : history[k].status = InvalidStatus}}

CommittedRw   == {i \in RwResponseIdx : history[i].tx_id \in CommittedTxIds}
CommittedResp == {i \in ResponseIdx : history[i].tx_id \in CommittedTxIds}

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

Observes(i, t) == \E k \in DOMAIN history[i].observed : history[i].observed[k] = t

-----------------------------------------------------------------------------
\* Invariants

\* Uniqueness
UniqueTxsInv ==
    \A b1, b2 \in DOMAIN ledgerBranches :
        \A k1 \in DOMAIN ledgerBranches[b1] : \A k2 \in DOMAIN ledgerBranches[b2] :
            ledgerBranches[b1][k1].tx = ledgerBranches[b2][k2].tx =>
                /\ k1 = k2
                /\ ledgerBranches[b1][k1].view = ledgerBranches[b2][k2].view

UniqueTxIdsInv ==
    \A i, j \in RwResponseIdx :
        history[i].tx_id = history[j].tx_id => i = j

UniqueTxRequestsInv ==
    \A i, j \in RequestIdx : history[i].tx = history[j].tx => i = j

UniqueSeqNumsCommittedInv ==
    \A a, b \in CommittedTxIds : a[2] = b[2] => a = b

\* Ordering
CommittedRwSerializableInv ==
    \A i, j \in CommittedRw :
        history[i].tx_id[2] <= history[j].tx_id[2] =>
            IsPrefix(history[i].observed, history[j].observed)

CommittedRwLinearizableInv ==
    \A i, j \in CommittedRw :
        \A r \in DOMAIN history :
            ( /\ history[r].type = RwTxRequest
              /\ history[r].tx = history[j].tx
              /\ i < r )
            => history[i].tx_id[2] < history[j].tx_id[2]

\* Observation
OnlyObserveSentRequestsInv ==
    \A i \in ResponseIdx :
        \A k \in DOMAIN history[i].observed :
            \E r \in DOMAIN history :
                /\ history[r].type = RwTxRequest
                /\ history[r].tx = history[i].observed[k]

AllCommittedObservedInv ==
    \A i \in CommittedRw : \A j \in CommittedResp :
        \A r \in RequestIdx :
            (history[r].tx = history[j].tx /\ i < r) => Observes(j, history[i].tx)

InvalidNotObservedByCommittedInv ==
    \A i \in RwResponseIdx :
        history[i].tx_id \in InvalidTxIds =>
            \A j \in CommittedResp : ~Observes(j, history[i].tx)

\* Consistency
AllReceivedIsFirstSentInv ==
    \A i \in ResponseIdx :
        \E r \in 1..(i - 1) :
            /\ history[r].type = (IF history[i].type = RwTxResponse
                                  THEN RwTxRequest ELSE RoTxRequest)
            /\ history[r].tx = history[i].tx

ObservedConsistentInv ==
    \A i, j \in CommittedResp :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

OneStatusPerTxIdInv ==
    CommittedTxIds \cap InvalidTxIds = {}

StatusOnlyForResponsesInv ==
    \A s \in StatusIdx :
        \E i \in 1..(s - 1) : IsResponse(i) /\ history[i].tx_id = history[s].tx_id

AllInvariants ==
    /\ UniqueTxsInv
    /\ UniqueTxIdsInv
    /\ UniqueTxRequestsInv
    /\ UniqueSeqNumsCommittedInv
    /\ CommittedRwSerializableInv
    /\ CommittedRwLinearizableInv
    /\ OnlyObserveSentRequestsInv
    /\ AllCommittedObservedInv
    /\ InvalidNotObservedByCommittedInv
    /\ AllReceivedIsFirstSentInv
    /\ ObservedConsistentInv
    /\ OneStatusPerTxIdInv
    /\ StatusOnlyForResponsesInv

THEOREM Spec => []AllInvariants

=============================================================================