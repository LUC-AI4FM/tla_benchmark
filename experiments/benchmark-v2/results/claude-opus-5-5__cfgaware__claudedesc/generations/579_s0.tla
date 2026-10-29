---- MODULE MCMultiNode ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANTS FirstBranch, HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

Range(s) == {s[k] : k \in DOMAIN s}

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

ViewOf(b) == FirstBranch + b - 1

CurrentView == ViewOf(Len(ledgerBranches))

Ledger == ledgerBranches[Len(ledgerBranches)]

TxsInLedger == {Ledger[k].tx : k \in DOMAIN Ledger}

IsType(i, t) == history[i].type = t

IsResponse(i) == history[i].type \in {RwTxResponse, RoTxResponse}

IsRequest(i) == history[i].type \in {RwTxRequest, RoTxRequest}

IsStatus(i, st) == history[i].type = TxStatusReceived /\ history[i].status = st

StatusExists(tid) ==
    \E k \in DOMAIN history : history[k].type = TxStatusReceived /\ history[k].tx_id = tid

HasResponse(tp, tx) ==
    \E k \in DOMAIN history : history[k].type = tp /\ history[k].tx = tx

CommittedSeqNums ==
    {history[k].tx_id[2] : k \in {j \in DOMAIN history : IsStatus(j, CommittedStatus)}}

MaxCommitted ==
    IF CommittedSeqNums = {} THEN 0
    ELSE CHOOSE m \in CommittedSeqNums : \A n \in CommittedSeqNums : n <= m

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ IsType(i, RwTxRequest)
        /\ history[i].tx \notin TxsInLedger
        /\ ~HasResponse(RwTxResponse, history[i].tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(Ledger, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN Ledger :
        /\ ~HasResponse(RwTxResponse, Ledger[i].tx)
        /\ history' = Append(history,
                [type |-> RwTxResponse,
                 tx |-> Ledger[i].tx,
                 observed |-> [j \in 1..i |-> Ledger[j].tx],
                 tx_id |-> <<Ledger[i].view, i>>])
    /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ Len(Ledger) > 0
    /\ \E i \in DOMAIN history :
        /\ IsType(i, RoTxRequest)
        /\ ~HasResponse(RoTxResponse, history[i].tx)
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> [j \in DOMAIN Ledger |-> Ledger[j].tx],
                 tx_id |-> <<Ledger[Len(Ledger)].view, Len(Ledger)>>])
    /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ IsType(i, RwTxResponse)
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ s \in DOMAIN Ledger
              /\ Ledger[s].view = v
              /\ ~StatusExists(history[i].tx_id)
              /\ history' = Append(history,
                    [type |-> TxStatusReceived,
                     tx_id |-> history[i].tx_id,
                     status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

SingleNodeActions ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ StatusCommittedResponseAction

\* View change: a new branch is formed from a prefix of the current ledger
\* that retains every committed entry. Bounded by ViewLimit.
TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in MaxCommitted..Len(Ledger) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Ledger, 1, i))
    /\ UNCHANGED history

\* Client learns a transaction is invalid. Bounded by HistoryLimit.
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ IsType(i, RwTxResponse)
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ CurrentView > v
              /\ \/ s \notin DOMAIN Ledger
                 \/ Ledger[s].view # v
              /\ ~StatusExists(history[i].tx_id)
              /\ history' = Append(history,
                    [type |-> TxStatusReceived,
                     tx_id |-> history[i].tx_id,
                     status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

NextMultiNodeAction ==
    \/ SingleNodeActions
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

MCSpecMultiNode == Init /\ [][NextMultiNodeAction]_vars

----------------------------------------------------------------------------
\* Invariants

RequestTypeFor(t) == IF t = RwTxResponse THEN RwTxRequest ELSE RoTxRequest

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \E j \in 1..(i - 1) :
                /\ history[j].type = RequestTypeFor(history[i].type)
                /\ history[j].tx = history[i].tx

CommittedRwIdx ==
    {i \in DOMAIN history :
        /\ IsType(i, RwTxResponse)
        /\ \E k \in DOMAIN history :
            IsStatus(k, CommittedStatus) /\ history[k].tx_id = history[i].tx_id}

AllCommittedObservedInv ==
    \A k, a, r, q \in DOMAIN history :
        ( /\ IsStatus(k, CommittedStatus)
          /\ IsType(a, RwTxResponse)
          /\ history[a].tx_id = history[k].tx_id
          /\ IsResponse(r)
          /\ history[q].type = RequestTypeFor(history[r].type)
          /\ history[q].tx = history[r].tx
          /\ k < q )
        => history[a].tx \in Range(history[r].observed)

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \A t \in Range(history[i].observed) :
                \E j \in 1..(i - 1) : IsType(j, RwTxRequest) /\ history[j].tx = t

UniqueTxsInv ==
    \A b \in DOMAIN ledgerBranches :
        \A x, y \in DOMAIN ledgerBranches[b] :
            x # y => ledgerBranches[b][x].tx # ledgerBranches[b][y].tx

SameObservationsInv ==
    \A i, j \in DOMAIN history :
        (IsResponse(i) /\ IsResponse(j) /\ history[i].tx_id = history[j].tx_id)
            => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        (IsType(i, RwTxResponse) /\ IsType(j, RwTxResponse) /\ history[i].tx # history[j].tx)
            => history[i].tx_id # history[j].tx_id

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (IsRequest(i) /\ IsRequest(j) /\ i # j) => history[i].tx # history[j].tx

UniqueSeqNumsCommittedInv ==
    \A i, j \in DOMAIN history :
        (IsStatus(i, CommittedStatus) /\ IsStatus(j, CommittedStatus)
            /\ history[i].tx_id # history[j].tx_id)
            => history[i].tx_id[2] # history[j].tx_id[2]

CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history :
        (IsStatus(i, CommittedStatus) /\ IsStatus(j, InvalidStatus))
            => history[i].tx_id # history[j].tx_id

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwIdx :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

InvalidNotObservedByCommittedInv ==
    \A i \in CommittedRwIdx :
        \A k, a \in DOMAIN history :
            (IsStatus(k, InvalidStatus) /\ IsType(a, RwTxResponse)
                /\ history[a].tx_id = history[k].tx_id)
                => history[a].tx \notin Range(history[i].observed)

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResponse(i) =>
            \A x, y \in DOMAIN history[i].observed :
                x # y => history[i].observed[x] # history[i].observed[y]

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j \in CommittedRwIdx :
        (\E q \in DOMAIN history :
            q > i /\ IsType(q, RwTxRequest) /\ history[q].tx = history[j].tx)
            => history[i].tx_id[2] < history[j].tx_id[2]

====