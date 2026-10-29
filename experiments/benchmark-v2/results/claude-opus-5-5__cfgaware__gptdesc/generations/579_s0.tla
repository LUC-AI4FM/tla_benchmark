---------------------------- MODULE MCMultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse, TxStatusReceived
CONSTANTS CommittedStatus, InvalidStatus
CONSTANT FirstBranch
CONSTANT HistoryLimit
CONSTANT ViewLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

----------------------------------------------------------------------------
\* Helpers

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

IsPrefix(a, b) == Len(a) <= Len(b) /\ SubSeq(b, 1, Len(a)) = a

LatestBranch == ledgerBranches[Len(ledgerBranches)]

CurrentView == FirstBranch + Len(ledgerBranches) - 1

BranchTxs(b, n) == [k \in 1..n |-> b[k].tx]

IsRequest(e) == e.type \in {RwTxRequest, RoTxRequest}

IsResponse(e) == e.type \in {RwTxResponse, RoTxResponse}

IsCommittedStatus(e) == e.type = TxStatusReceived /\ e.status = CommittedStatus

IsInvalidStatus(e) == e.type = TxStatusReceived /\ e.status = InvalidStatus

Responded(t) ==
    \E i \in DOMAIN history : IsResponse(history[i]) /\ history[i].tx = t

InLatest(t) ==
    \E k \in DOMAIN LatestBranch : LatestBranch[k].tx = t

MatchesLatest(txid) ==
    /\ txid[2] \in DOMAIN LatestBranch
    /\ LatestBranch[txid[2]].view = txid[1]

HasStatus(txid) ==
    \E i \in DOMAIN history :
        /\ history[i].type = TxStatusReceived
        /\ history[i].tx_id = txid

Committed(txid) ==
    \E i \in DOMAIN history :
        /\ IsCommittedStatus(history[i])
        /\ history[i].tx_id = txid

Invalid(txid) ==
    \E i \in DOMAIN history :
        /\ IsInvalidStatus(history[i])
        /\ history[i].tx_id = txid

CommittedIndex ==
    LET S == { history[i].tx_id[2] :
                 i \in { j \in DOMAIN history : IsCommittedStatus(history[j]) } }
    IN IF S = {} THEN 0 ELSE Max(S)

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

----------------------------------------------------------------------------
\* Actions

RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history)])
    /\ UNCHANGED ledgerBranches

RoTxRequestAction ==
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> Len(history)])
    /\ UNCHANGED ledgerBranches

RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~InLatest(history[i].tx)
        /\ ~Responded(history[i].tx)
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
        /\ UNCHANGED history

RwTxResponseAction ==
    \E k \in DOMAIN LatestBranch :
        /\ ~Responded(LatestBranch[k].tx)
        /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> LatestBranch[k].tx,
                 observed |-> BranchTxs(LatestBranch, k),
                 tx_id    |-> <<LatestBranch[k].view, k>>])
        /\ UNCHANGED ledgerBranches

RoTxResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~Responded(history[i].tx)
        /\ history' = Append(history,
                [type     |-> RoTxResponse,
                 tx       |-> history[i].tx,
                 observed |-> BranchTxs(LatestBranch, Len(LatestBranch)),
                 tx_id    |-> <<CurrentView, Len(LatestBranch)>>])
        /\ UNCHANGED ledgerBranches

StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ MatchesLatest(history[i].tx_id)
        /\ ~HasStatus(history[i].tx_id)
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

StatusInvalidResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~MatchesLatest(history[i].tx_id)
        /\ ~HasStatus(history[i].tx_id)
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> InvalidStatus])
        /\ UNCHANGED ledgerBranches

TruncateLedgerAction ==
    \E i \in CommittedIndex..Len(LatestBranch) :
        /\ ledgerBranches' = Append(ledgerBranches, SubSeq(LatestBranch, 1, i))
        /\ UNCHANGED history

----------------------------------------------------------------------------
\* Bounded variants for model checking

MCRwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxRequestAction

MCRoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxRequestAction

MCRwTxExecuteAction ==
    /\ Len(history) <= HistoryLimit
    /\ RwTxExecuteAction

MCRwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RwTxResponseAction

MCRoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ RoTxResponseAction

MCStatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusCommittedResponseAction

MCStatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ StatusInvalidResponseAction

MCTruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ TruncateLedgerAction

MCNextMultiNodeAction ==
    \/ MCRwTxRequestAction
    \/ MCRoTxRequestAction
    \/ MCRwTxExecuteAction
    \/ MCRwTxResponseAction
    \/ MCRoTxResponseAction
    \/ MCStatusCommittedResponseAction
    \/ MCStatusInvalidResponseAction
    \/ MCTruncateLedgerAction

MCSpecMultiNode == Init /\ [][MCNextMultiNodeAction]_vars

----------------------------------------------------------------------------
\* Invariants

AllReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \E j \in 1..(i-1) :
                /\ IsRequest(history[j])
                /\ history[j].tx = history[i].tx

AllCommittedObservedInv ==
    \A i \in DOMAIN history :
        IsCommittedStatus(history[i]) =>
            \E j \in 1..(i-1) :
                /\ history[j].type = RwTxResponse
                /\ history[j].tx_id = history[i].tx_id

OnlyObserveSentRequestsInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \A k \in DOMAIN history[i].observed :
                \E j \in 1..(i-1) :
                    /\ history[j].type = RwTxRequest
                    /\ history[j].tx = history[i].observed[k]

UniqueTxsInv ==
    \A i, j \in DOMAIN history :
        (/\ IsResponse(history[i])
         /\ IsResponse(history[j])
         /\ history[i].tx = history[j].tx) => i = j

SameObservationsInv ==
    \A i, j \in DOMAIN history :
        (/\ IsResponse(history[i])
         /\ IsResponse(history[j])
         /\ history[i].tx_id = history[j].tx_id)
            => history[i].observed = history[j].observed

UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx_id = history[j].tx_id) => i = j

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (/\ IsRequest(history[i])
         /\ IsRequest(history[j])
         /\ history[i].tx = history[j].tx) => i = j

UniqueSeqNumsCommittedInv ==
    \A i, j \in DOMAIN history :
        (/\ IsCommittedStatus(history[i])
         /\ IsCommittedStatus(history[j])
         /\ history[i].tx_id[2] = history[j].tx_id[2])
            => history[i].tx_id = history[j].tx_id

CommittedOrInvalidStrongInv ==
    \A i, j \in DOMAIN history :
        (/\ IsCommittedStatus(history[i])
         /\ IsInvalidStatus(history[j]))
            => history[i].tx_id # history[j].tx_id

CommittedRwSerializableInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ Committed(history[i].tx_id)
         /\ Committed(history[j].tx_id)
         /\ history[i].tx_id[2] <= history[j].tx_id[2])
            => IsPrefix(history[i].observed, history[j].observed)

InvalidNotObservedByCommittedInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ Invalid(history[i].tx_id)
         /\ history[j].type = RwTxResponse
         /\ Committed(history[j].tx_id))
            => \A k \in DOMAIN history[j].observed :
                   history[j].observed[k] # history[i].tx

AtMostOnceObservedInv ==
    \A i \in DOMAIN history :
        IsResponse(history[i]) =>
            \A k1, k2 \in DOMAIN history[i].observed :
                history[i].observed[k1] = history[i].observed[k2] => k1 = k2

CommittedRwOrderedSpecLinearizableInv ==
    \A i, j, k \in DOMAIN history :
        (/\ i < j
         /\ history[i].type = RwTxResponse
         /\ Committed(history[i].tx_id)
         /\ history[j].type = RwTxRequest
         /\ history[k].type = RwTxResponse
         /\ history[k].tx = history[j].tx
         /\ Committed(history[k].tx_id))
            => history[i].tx_id[2] < history[k].tx_id[2]

=============================================================================