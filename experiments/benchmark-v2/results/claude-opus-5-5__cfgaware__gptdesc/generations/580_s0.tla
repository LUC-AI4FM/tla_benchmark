---------------------------- MODULE MCSingleNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    RwTxRequest, RwTxResponse,
    RoTxRequest, RoTxResponse,
    TxStatusReceived,
    CommittedStatus, InvalidStatus

CONSTANT FirstBranch
CONSTANT HistoryLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------------------------------------------------------------------
\* Helpers

Range(s) == {s[i] : i \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

LatestBranch == ledgerBranches[Len(ledgerBranches)]

NextRequestId ==
    Cardinality({i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}})

IsCommitted(txid) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].status = CommittedStatus
        /\ history[i].tx_id = txid

IsInvalid(txid) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].status = InvalidStatus
        /\ history[i].tx_id = txid

HasStatus(txid) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].tx_id = txid

CommittedSeqnums ==
    {history[i].tx_id[2] : i \in {k \in DOMAIN history :
        /\ history[k].type = TxStatusReceived
        /\ history[k].status = CommittedStatus}}

MaxCommittedSeqnum ==
    IF CommittedSeqnums = {} THEN 0
    ELSE CHOOSE m \in CommittedSeqnums : \A n \in CommittedSeqnums : n <= m

RwResponses == {i \in DOMAIN history : history[i].type = RwTxResponse}
RoResponses == {i \in DOMAIN history : history[i].type = RoTxResponse}
AllResponses == RwResponses \cup RoResponses

CommittedRwResponses == {i \in RwResponses : IsCommitted(history[i].tx_id)}
CommittedRoResponses == {i \in RoResponses : IsCommitted(history[i].tx_id)}
InvalidRwResponses == {i \in RwResponses : IsInvalid(history[i].tx_id)}

\* ---------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..FirstBranch |-> <<>>]

\* ---------------------------------------------------------------------------
\* Actions

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A k \in DOMAIN LatestBranch : LatestBranch[k].tx # history[i].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(@, [view |-> Len(ledgerBranches), tx |-> history[i].tx])]
        /\ UNCHANGED history

RwTxResponseAction ==
    \E view \in FirstBranch..Len(ledgerBranches) :
        \E seqnum \in DOMAIN ledgerBranches[view] :
            LET e == ledgerBranches[view][seqnum] IN
            /\ e.view = view
            /\ \A i \in DOMAIN history :
                    history[i].type = RwTxResponse => history[i].tx # e.tx
            /\ history' = Append(history,
                    [type |-> RwTxResponse,
                     tx |-> e.tx,
                     observed |-> [x \in 1..seqnum |-> ledgerBranches[view][x].tx],
                     tx_id |-> <<e.view, seqnum>>])
            /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    /\ Len(LatestBranch) > 0
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A j \in DOMAIN history :
                history[j].type = RoTxResponse => history[j].tx # history[i].tx
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [x \in 1..Len(LatestBranch) |-> LatestBranch[x].tx],
                 tx_id |-> <<LatestBranch[Len(LatestBranch)].view, Len(LatestBranch)>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    \E i \in AllResponses :
        LET v == history[i].tx_id[1]
            s == history[i].tx_id[2]
        IN
        /\ ~HasStatus(history[i].tx_id)
        /\ s \in DOMAIN LatestBranch
        /\ LatestBranch[s].view = v
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    \E i \in AllResponses :
        LET v == history[i].tx_id[1]
            s == history[i].tx_id[2]
        IN
        /\ ~HasStatus(history[i].tx_id)
        /\ s \in DOMAIN LatestBranch
        /\ LatestBranch[s].view # v
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
                 status |-> InvalidStatus])
        /\ UNCHANGED ledgerBranches

TruncateLedgerAction ==
    \E i \in MaxCommittedSeqnum..Len(LatestBranch) :
        /\ ledgerBranches' = Append(ledgerBranches, SubSeq(LatestBranch, 1, i))
        /\ UNCHANGED history

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

\* ---------------------------------------------------------------------------
\* Model-checking bounded actions

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < FirstBranch + HistoryLimit
    /\ TruncateLedgerAction

MCNextSingleNodeAction ==
    \/ MCRwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ MCTruncateLedgerAction

MCRoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxRequestAction

MCRoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxResponseAction

MCNextSingleNodeReadsAction ==
    \/ MCNextSingleNodeAction
    \/ MCRoTxRequestAction
    \/ MCRoTxResponseAction

MCSpecSingleNodeReads == Init /\ [][MCNextSingleNodeReadsAction]_vars

\* ---------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    \A i \in AllResponses :
        \E j \in DOMAIN history :
            /\ j < i
            /\ history[j].type \in {RwTxRequest, RoTxRequest}
            /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A j, k \in CommittedRwResponses :
        history[j].tx_id[2] < history[k].tx_id[2]
            => history[j].tx \in Range(history[k].observed)

OnlyObserveSentRequestsInv ==
    \A i \in AllResponses :
        \A t \in Range(history[i].observed) :
            \E j \in DOMAIN history :
                /\ j < i
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in RwResponses :
        history[i].tx = history[j].tx => i = j

UniqueTxIdsInv ==
    \A i, j \in RwResponses :
        history[i].tx_id = history[j].tx_id => i = j

UniqueSeqNumsInv ==
    \A i, j \in CommittedRwResponses :
        history[i].tx_id[2] = history[j].tx_id[2] => i = j

CommittedOrInvalidStrongInv ==
    \A i \in AllResponses :
        ~(IsCommitted(history[i].tx_id) /\ IsInvalid(history[i].tx_id))

RwSerializableInv ==
    \A i, j \in RwResponses :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResponses :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A i \in InvalidRwResponses :
        \A j \in AllResponses :
            history[i].tx \notin Range(history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in InvalidRwResponses :
        \A j \in CommittedRwResponses \cup CommittedRoResponses :
            history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in AllResponses :
        \A x, y \in DOMAIN history[i].observed :
            history[i].observed[x] = history[i].observed[y] => x = y

AllCommittedObservedRoInv ==
    \A i \in CommittedRoResponses :
        \A j \in CommittedRwResponses :
            history[j].tx_id[2] <= history[i].tx_id[2]
                => history[j].tx \in Range(history[i].observed)

=============================================================================