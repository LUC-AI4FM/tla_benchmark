---------------------------- MODULE MCMultiNodeReads ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANTS HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

FirstBranch == 1

Range(f) == {f[x] : x \in DOMAIN f}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

Ledger == ledgerBranches[Len(ledgerBranches)]

CurrentView == Len(ledgerBranches)

IsStatus(i) == history[i].type = TxStatusReceived

IsCommittedStatus(i) == IsStatus(i) /\ history[i].status = CommittedStatus

IsInvalidStatus(i) == IsStatus(i) /\ history[i].status = InvalidStatus

CommittedTxIds == {history[i].tx_id : i \in {k \in DOMAIN history : IsCommittedStatus(k)}}

InvalidTxIds == {history[i].tx_id : i \in {k \in DOMAIN history : IsInvalidStatus(k)}}

StatusKnown(tid) == \E k \in DOMAIN history : IsStatus(k) /\ history[k].tx_id = tid

CommittedSeqNums == {tid[2] : tid \in CommittedTxIds}

MaxCommittedSeqNum ==
    IF CommittedSeqNums = {} THEN 0
    ELSE CHOOSE m \in CommittedSeqNums : \A n \in CommittedSeqNums : n <= m

Responded(type, tx) == \E k \in DOMAIN history : history[k].type = type /\ history[k].tx = tx

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..FirstBranch |-> <<>>]

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A k \in DOMAIN Ledger : Ledger[k].tx # history[i].tx
        /\ ~Responded(RwTxResponse, history[i].tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                                Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN Ledger :
        /\ ~Responded(RwTxResponse, Ledger[i].tx)
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> Ledger[i].tx,
                 observed |-> [x \in 1..i |-> Ledger[x].tx],
                 tx_id |-> <<Ledger[i].view, i>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN Ledger :
        /\ \E k \in DOMAIN history :
            /\ history[k].type = RwTxResponse
            /\ history[k].tx_id = <<Ledger[i].view, i>>
        /\ ~StatusKnown(<<Ledger[i].view, i>>)
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> <<Ledger[i].view, i>>,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E k \in DOMAIN history :
        /\ history[k].type = RwTxResponse
        /\ LET tid == history[k].tx_id IN
            /\ ~StatusKnown(tid)
            /\ \/ (tid[2] <= Len(Ledger) /\ Ledger[tid[2]].view # tid[1])
               \/ (tid[1] < CurrentView /\ tid[2] > Len(Ledger))
            /\ history' = Append(history,
                    [type |-> TxStatusReceived,
                     tx_id |-> tid,
                     status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in MaxCommittedSeqNum..Len(Ledger) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Ledger, 1, i))
    /\ UNCHANGED history

NextMultiNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

-----------------------------------------------------------------------------
RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~Responded(RoTxResponse, history[i].tx)
        /\ \E s \in DOMAIN Ledger :
            history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [x \in 1..s |-> Ledger[x].tx],
                 tx_id |-> <<Ledger[s].view, s>>])
    /\ UNCHANGED ledgerBranches

NextMultiNodeReadsAction ==
    \/ NextMultiNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

MCSpecMultiNodeReads == Init /\ [][NextMultiNodeReadsAction]_vars

-----------------------------------------------------------------------------
IsResponse(i) == history[i].type \in {RwTxResponse, RoTxResponse}

IsRequest(i) == history[i].type \in {RwTxRequest, RoTxRequest}

CommittedRwResponses ==
    {i \in DOMAIN history : history[i].type = RwTxResponse /\ history[i].tx_id \in CommittedTxIds}

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \E j \in 1..(i-1) : IsRequest(j) /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j \in DOMAIN history :
        (/\ IsCommittedStatus(i)
         /\ i < j
         /\ history[j].type = RwTxResponse
         /\ history[j].tx_id[2] >= history[i].tx_id[2])
        => \E k \in DOMAIN history :
              /\ history[k].type = RwTxResponse
              /\ history[k].tx_id = history[i].tx_id
              /\ history[k].tx \in Range(history[j].observed)

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \A t \in Range(history[i].observed) :
                \E j \in 1..(i-1) : history[j].type = RwTxRequest /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        (/\ IsResponse(i) /\ IsResponse(j)
         /\ history[i].type = history[j].type
         /\ history[i].tx = history[j].tx) => i = j

SameObservationsInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id = history[j].tx_id)
        => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id = history[j].tx_id) => i = j

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (/\ IsRequest(i) /\ IsRequest(j)
         /\ history[i].tx = history[j].tx) => i = j

UniqueSeqNumsCommittedInv ==
    \A t1, t2 \in CommittedTxIds : t1[2] = t2[2] => t1 = t2

CommittedOrInvalidStrongInv ==
    CommittedTxIds \cap InvalidTxIds = {}

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResponses :
        IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in DOMAIN history :
        \A j \in CommittedRwResponses :
            (history[i].type = RwTxResponse /\ history[i].tx_id \in InvalidTxIds)
            => history[i].tx \notin Range(history[j].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \A a, b \in DOMAIN history[i].observed :
                history[i].observed[a] = history[i].observed[b] => a = b

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwResponses :
        (\E r \in DOMAIN history :
            /\ history[r].type = RwTxRequest
            /\ history[r].tx = history[j].tx
            /\ i < r)
        => history[i].tx \in Range(history[j].observed)

=============================================================================