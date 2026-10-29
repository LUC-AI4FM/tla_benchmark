---- MODULE MCMultiNodeReadsAlt ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS FirstBranch, HistoryLimit, ViewLimit

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived

CONSTANTS CommittedStatus, InvalidStatus

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

CurrentView == FirstBranch + Len(ledgerBranches) - 1

CurrentBranch == ledgerBranches[Len(ledgerBranches)]

Branch(v) == ledgerBranches[v - FirstBranch + 1]

IsRequest(e) == e.type \in {RwTxRequest, RoTxRequest}

IsResponse(e) == e.type \in {RwTxResponse, RoTxResponse}

IsStatus(e) == e.type = TxStatusReceived

NextTx == Cardinality({i \in DOMAIN history : IsRequest(history[i])})

IsResponded(t) ==
    \E i \in DOMAIN history : IsResponse(history[i]) /\ history[i].tx = t

IsExecuted(t) ==
    \E k \in DOMAIN ledgerBranches :
        \E j \in DOMAIN ledgerBranches[k] : ledgerBranches[k][j].tx = t

TxsOf(s) == [k \in DOMAIN s |-> s[k].tx]

StatusKnown(tid) ==
    \E i \in DOMAIN history : IsStatus(history[i]) /\ history[i].tx_id = tid

IsCommitted(tid) ==
    \E i \in DOMAIN history :
        /\ IsStatus(history[i])
        /\ history[i].tx_id = tid
        /\ history[i].status = CommittedStatus

IsInvalid(tid) ==
    \E i \in DOMAIN history :
        /\ IsStatus(history[i])
        /\ history[i].tx_id = tid
        /\ history[i].status = InvalidStatus

CommittedSeqNums ==
    { history[i].tx_id[2] :
        i \in { k \in DOMAIN history :
                    IsStatus(history[k]) /\ history[k].status = CommittedStatus } }

MaxCommitted ==
    IF CommittedSeqNums = {} THEN 0
    ELSE CHOOSE m \in CommittedSeqNums : \A n \in CommittedSeqNums : n <= m

InSeq(x, s) == \E n \in DOMAIN s : s[n] = x

\* ---------------------------------------------------------------------------
\* Base initial state and actions
\* ---------------------------------------------------------------------------

MultiNodeReadsInit ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextTx])
    /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextTx])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~IsExecuted(history[i].tx)
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E v \in FirstBranch..CurrentView :
        \E j \in DOMAIN Branch(v) :
            /\ Branch(v)[j].view = v
            /\ ~IsResponded(Branch(v)[j].tx)
            /\ history' = Append(history,
                    [type |-> RwTxResponse,
                     tx |-> Branch(v)[j].tx,
                     observed |-> TxsOf(SubSeq(Branch(v), 1, j - 1)),
                     tx_id |-> <<v, j>>])
    /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~IsResponded(history[i].tx)
        /\ \E k \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[k]) > 0
            /\ history' = Append(history,
                    [type |-> RoTxResponse,
                     tx |-> history[i].tx,
                     observed |-> TxsOf(ledgerBranches[k]),
                     tx_id |-> <<ledgerBranches[k][Len(ledgerBranches[k])].view,
                                 Len(ledgerBranches[k])>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~StatusKnown(history[i].tx_id)
        /\ history[i].tx_id[2] <= Len(CurrentBranch)
        /\ CurrentBranch[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~StatusKnown(history[i].tx_id)
        /\ history[i].tx_id[1] < CurrentView
        /\ ~ ( /\ history[i].tx_id[2] <= Len(CurrentBranch)
               /\ CurrentBranch[history[i].tx_id[2]].view = history[i].tx_id[1] )
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in MaxCommitted..Len(CurrentBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, i))
    /\ UNCHANGED history

NextMultiNodeReadsAction ==
    \/ RwTxRequestAction
    \/ RoTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction
    \/ TruncateLedgerAction

MCNextMultiNodeReadsAction == NextMultiNodeReadsAction

MCSpecMultiNodeReads == MultiNodeReadsInit /\ [][MCNextMultiNodeReadsAction]_vars

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \E j \in 1..(i - 1) :
                /\ IsRequest(history[j])
                /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i, j, k \in DOMAIN history :
        ( /\ IsStatus(history[i])
          /\ history[i].status = CommittedStatus
          /\ history[j].type = RwTxResponse
          /\ history[j].tx_id = history[i].tx_id
          /\ history[k].type = RwTxResponse
          /\ k > i
          /\ \E r \in DOMAIN history :
                /\ r > i
                /\ history[r].type = RwTxRequest
                /\ history[r].tx = history[k].tx )
        => InSeq(history[j].tx, history[k].observed)

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \A n \in DOMAIN history[i].observed :
                \E j \in 1..(i - 1) :
                    /\ history[j].type = RwTxRequest
                    /\ history[j].tx = history[i].observed[n]

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsResponse(history[i])
          /\ IsResponse(history[j])
          /\ history[i].tx = history[j].tx )
        => i = j

SameObservationsInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsResponse(history[i])
          /\ IsResponse(history[j])
          /\ history[i].type = history[j].type
          /\ history[i].tx_id = history[j].tx_id )
        => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse
          /\ history[i].tx_id = history[j].tx_id )
        => i = j

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsRequest(history[i])
          /\ IsRequest(history[j])
          /\ history[i].tx = history[j].tx )
        => i = j

UniqueSeqNumsCommittedInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsStatus(history[i])
          /\ IsStatus(history[j])
          /\ history[i].status = CommittedStatus
          /\ history[j].status = CommittedStatus
          /\ history[i].tx_id[2] = history[j].tx_id[2] )
        => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history :
        ( /\ IsStatus(history[i])
          /\ IsStatus(history[j])
          /\ history[i].tx_id = history[j].tx_id )
        => history[i].status = history[j].status

CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse
          /\ IsCommitted(history[i].tx_id)
          /\ IsCommitted(history[j].tx_id)
          /\ history[i].tx_id[2] < history[j].tx_id[2] )
        => InSeq(history[i].tx, history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse
          /\ IsInvalid(history[i].tx_id)
          /\ IsCommitted(history[j].tx_id) )
        => ~InSeq(history[i].tx, history[j].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \A a, b \in DOMAIN history[i].observed :
                history[i].observed[a] = history[i].observed[b] => a = b

\* ---------------------------------------------------------------------------
\* Alternative initial state where two transactions have been committed
\* ---------------------------------------------------------------------------

MultiNodeReadsAltInit ==
    /\ ledgerBranches =
        << << [view |-> FirstBranch, tx |-> 0],
              [view |-> FirstBranch, tx |-> 1] >> >>
    /\ history = <<
        [type |-> RwTxRequest, tx |-> 0],
        [type |-> RwTxResponse, tx |-> 0, observed |-> <<>>,
            tx_id |-> <<FirstBranch, 1>>],
        [type |-> RwTxRequest, tx |-> 1],
        [type |-> RwTxResponse, tx |-> 1, observed |-> <<0>>,
            tx_id |-> <<FirstBranch, 2>>],
        [type |-> TxStatusReceived, tx_id |-> <<FirstBranch, 1>>,
            status |-> CommittedStatus],
        [type |-> TxStatusReceived, tx_id |-> <<FirstBranch, 2>>,
            status |-> CommittedStatus]
        >>

MCSpecMultiNodeReadsAlt ==
    MultiNodeReadsAltInit /\ [][MCNextMultiNodeReadsAction]_vars

====