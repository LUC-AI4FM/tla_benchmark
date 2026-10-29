---- MODULE MCSingleNodeReads ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxRequest,
    RwTxResponse,
    RoTxRequest,
    RoTxResponse,
    TxStatusReceived,
    CommittedStatus,
    InvalidStatus,
    FirstBranch,
    HistoryLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

Range(s) == {s[i] : i \in DOMAIN s}

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

CurrentView == FirstBranch

Ledger == ledgerBranches[FirstBranch]

HistoryNotFull == Len(history) < HistoryLimit

ReqType(rt) == IF rt = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

IsRwReq(i) == history[i].type = RwTxRequest
IsRoReq(i) == history[i].type = RoTxRequest
IsRwResp(i) == history[i].type = RwTxResponse
IsRoResp(i) == history[i].type = RoTxResponse
IsResp(i) == history[i].type \in {RwTxResponse, RoTxResponse}
IsStatus(i) == history[i].type = TxStatusReceived
IsCommitted(i) == IsStatus(i) /\ history[i].status = CommittedStatus
IsInvalid(i) == IsStatus(i) /\ history[i].status = InvalidStatus

Responded(t, rtype) ==
    \E j \in DOMAIN history : history[j].type = rtype /\ history[j].tx = t

HasStatus(tid) ==
    \E j \in DOMAIN history : IsStatus(j) /\ history[j].tx_id = tid

CommittedResp(i) ==
    IsResp(i) /\ \E j \in DOMAIN history :
                    IsCommitted(j) /\ history[j].tx_id = history[i].tx_id

CommittedRwResp(i) == IsRwResp(i) /\ CommittedResp(i)

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in {FirstBranch} |-> <<>>]

\* ---------------------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------------------

\* Client submits a read-write transaction
RwTxRequestAction ==
    /\ HistoryNotFull
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* Node executes a read-write transaction, appending it to its ledger
ExecuteRwTxAction ==
    /\ \E i \in DOMAIN history :
        /\ IsRwReq(i)
        /\ history[i].tx \notin Range(Ledger)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![FirstBranch] = Append(@, history[i].tx)]
    /\ UNCHANGED history

\* Node replies to a read-write transaction that it has executed
RwTxResponseAction ==
    /\ HistoryNotFull
    /\ \E s \in DOMAIN Ledger :
        /\ \E i \in DOMAIN history : IsRwReq(i) /\ history[i].tx = Ledger[s]
        /\ ~Responded(Ledger[s], RwTxResponse)
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> Ledger[s],
                 observed |-> SubSeq(Ledger, 1, s),
                 tx_id |-> <<CurrentView, s>>])
    /\ UNCHANGED ledgerBranches

\* Client submits a read-only transaction
RoTxRequestAction ==
    /\ HistoryNotFull
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* Node replies to a read-only transaction; linearization point is now
RoTxResponseAction ==
    /\ HistoryNotFull
    /\ \E i \in DOMAIN history :
        /\ IsRoReq(i)
        /\ ~Responded(history[i].tx, RoTxResponse)
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> Ledger,
                 tx_id |-> <<CurrentView, Len(Ledger)>>])
    /\ UNCHANGED ledgerBranches

\* Client learns that a transaction is committed (single node commits at once)
StatusCommittedAction ==
    /\ HistoryNotFull
    /\ \E i \in DOMAIN history :
        /\ IsResp(i)
        /\ history[i].tx_id[1] = CurrentView
        /\ history[i].tx_id[2] <= Len(Ledger)
        /\ ~HasStatus(history[i].tx_id)
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Client learns that a transaction is invalid (only possible for foreign views)
StatusInvalidAction ==
    /\ HistoryNotFull
    /\ \E i \in DOMAIN history :
        /\ IsResp(i)
        /\ history[i].tx_id[1] # CurrentView
        /\ ~HasStatus(history[i].tx_id)
        /\ history' = Append(history,
                [type |-> TxStatusReceived,
                 tx_id |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

\* Step when nothing else happens
Stutter == UNCHANGED vars

Next ==
    \/ RwTxRequestAction
    \/ ExecuteRwTxAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ StatusCommittedAction
    \/ StatusInvalidAction
    \/ Stutter

Fairness ==
    /\ WF_vars(ExecuteRwTxAction)
    /\ WF_vars(RwTxResponseAction)
    /\ WF_vars(RoTxResponseAction)

SpecSingleNodeReads == Init /\ [][Next]_vars /\ Fairness

MCSpecSingleNodeReads == SpecSingleNodeReads

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

HistoryBoundInv == Len(history) <= HistoryLimit

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = ReqType(history[i].type)
                /\ history[j].tx = history[i].tx

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            \A t \in Range(history[i].observed) :
                \E j \in 1..(i - 1) : IsRwReq(j) /\ history[j].tx = t

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        (IsResp(i) /\ IsResp(j) /\ history[i].tx = history[j].tx) => i = j

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        (IsRwResp(i) /\ IsRwResp(j) /\ history[i].tx_id = history[j].tx_id) => i = j

UniqueSeqNumsInv ==
    \A i, j \in DOMAIN history :
        (IsCommitted(i) /\ IsCommitted(j) /\ history[i].tx_id[2] = history[j].tx_id[2])
            => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history :
        (IsCommitted(i) /\ IsInvalid(j)) =>
            /\ history[i].tx_id # history[j].tx_id
            /\ ~(history[i].tx_id[1] = history[j].tx_id[1]
                 /\ history[j].tx_id[2] <= history[i].tx_id[2])

RwSerializableInv ==
    \A i, j \in DOMAIN history :
        (IsRwResp(i) /\ IsRwResp(j)) =>
            \/ IsPrefix(history[i].observed, history[j].observed)
            \/ IsPrefix(history[j].observed, history[i].observed)

CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history :
        (CommittedRwResp(i) /\ CommittedRwResp(j)) =>
            \/ IsPrefix(history[i].observed, history[j].observed)
            \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedInv ==
    \A i, j, k \in DOMAIN history :
        (/\ IsInvalid(i)
         /\ IsRwResp(j)
         /\ history[j].tx_id = history[i].tx_id
         /\ IsResp(k)
         /\ k > i)
        => history[j].tx \notin Range(history[k].observed)

InvalidNotObservedByCommittedInv ==
    \A i, j, k \in DOMAIN history :
        (/\ IsInvalid(i)
         /\ IsRwResp(j)
         /\ history[j].tx_id = history[i].tx_id
         /\ CommittedResp(k))
        => history[j].tx \notin Range(history[k].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResp(i) =>
            Len(history[i].observed) = Cardinality(Range(history[i].observed))

AllCommittedObservedInv ==
    \A i, j, k \in DOMAIN history :
        (/\ IsCommitted(i)
         /\ IsRwResp(j)
         /\ history[j].tx_id = history[i].tx_id
         /\ IsRwResp(k)
         /\ \E r \in DOMAIN history :
                r > i /\ IsRwReq(r) /\ history[r].tx = history[k].tx)
        => history[j].tx \in Range(history[k].observed)

AllCommittedObservedRoInv ==
    \A i, j, k \in DOMAIN history :
        (/\ IsCommitted(i)
         /\ IsRwResp(j)
         /\ history[j].tx_id = history[i].tx_id
         /\ IsRoResp(k)
         /\ \E r \in DOMAIN history :
                r > i /\ IsRoReq(r) /\ history[r].tx = history[k].tx)
        => history[j].tx \in Range(history[k].observed)

\* ---------------------------------------------------------------------------
\* Liveness (subject to the history bound)
\* ---------------------------------------------------------------------------

EventuallyRespondedOrFull ==
    \A t \in 1..HistoryLimit :
        [](  (\E i \in DOMAIN history : IsRwReq(i) /\ history[i].tx = t)
          => <>(Responded(t, RwTxResponse) \/ ~HistoryNotFull))

====