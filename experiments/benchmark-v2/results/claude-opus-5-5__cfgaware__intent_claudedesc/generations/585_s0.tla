---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Model bounds are operators, not CONSTANTs, so the module binds to a
\* configuration that only names the operators listed in the request.
HistoryLimit == 7
LedgerLimit  == 5
ViewLimit    == 1

\* Event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Status values
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

Views == 1..ViewLimit
SeqNums == Nat \ {0}
TxIDs == Views \X SeqNums
Txs == Nat \ {0}

Last(s) == s[Len(s)]

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A k \in 1..Len(s) : s[k] = t[k]

-----------------------------------------------------------------------------
\* Type and correctness properties

LedgerTypeOK ==
    /\ ledgerBranches \in Seq(Seq(UNION {
            [view : Views],
            [view : Views, tx : Txs]
        }))
    /\ \A v \in DOMAIN ledgerBranches :
        \A s \in DOMAIN ledgerBranches[v] :
            /\ ledgerBranches[v][s].view \in Views
            /\ "tx" \in DOMAIN ledgerBranches[v][s] =>
                    ledgerBranches[v][s].tx \in Txs

HistoryTypeOK ==
    \A i \in DOMAIN history :
        \/ /\ history[i].type = RwTxRequest
           /\ history[i].tx \in Txs
        \/ /\ history[i].type = RwTxResponse
           /\ history[i].tx \in Txs
           /\ history[i].tx_id \in TxIDs
           /\ history[i].observed \in Seq(Txs)
        \/ /\ history[i].type = TxStatusReceived
           /\ history[i].tx_id \in TxIDs
           /\ history[i].status \in {CommittedStatus, InvalidStatus}

TypeOK == LedgerTypeOK /\ HistoryTypeOK

\* Each ledger branch is append-only.
AppendOnlyProp ==
    [][\A v \in DOMAIN ledgerBranches :
          /\ v \in DOMAIN ledgerBranches'
          /\ IsPrefix(ledgerBranches[v], ledgerBranches'[v])]_ledgerBranches

\* Every recorded tx id remains valid forever, i.e. it is still present
\* at its expected position in the current ledger.
TxIdValid(txid) ==
    /\ Len(ledgerBranches) >= 1
    /\ Len(Last(ledgerBranches)) >= txid[2]
    /\ Last(ledgerBranches)[txid[2]].view = txid[1]

AllTxIdsStillValidInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse => TxIdValid(history[i].tx_id)

NoInvalidStatusInv ==
    \A i \in DOMAIN history :
        history[i].type = TxStatusReceived =>
            history[i].status # InvalidStatus

NoInvalidTxProp == [][AllTxIdsStillValidInv /\ NoInvalidStatusInv]_vars

-----------------------------------------------------------------------------
\* External history consistency

\* Every response is preceded by its request.
AllRwReceivedIsFirstSentInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            \E j \in 1..(i-1) :
                /\ history[j].type = RwTxRequest
                /\ history[j].tx = history[i].tx

\* At most one response per transaction.
UniqueResponseInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[j].type = RwTxResponse
        /\ history[i].tx = history[j].tx
        => i = j

\* Transaction ids are unique across responses.
UniqueTxIdsInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[j].type = RwTxResponse
        /\ history[i].tx_id = history[j].tx_id
        => i = j

\* Each response observes its own transaction last.
ObservedOwnTxInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            /\ Len(history[i].observed) >= 1
            /\ Last(history[i].observed) = history[i].tx

\* Committed status refers to a tx id that was returned in a response.
CommittedHasResponseInv ==
    \A i \in DOMAIN history :
        history[i].type = TxStatusReceived =>
            \E j \in 1..(i-1) :
                /\ history[j].type = RwTxResponse
                /\ history[j].tx_id = history[i].tx_id

CommittedResponses ==
    { j \in DOMAIN history :
        /\ history[j].type = RwTxResponse
        /\ \E k \in DOMAIN history :
            /\ history[k].type = TxStatusReceived
            /\ history[k].status = CommittedStatus
            /\ history[k].tx_id = history[j].tx_id }

\* Observations of committed transactions are linearly consistent.
AllCommittedObservedInv ==
    \A i, j \in CommittedResponses :
        \/ IsPrefix(history[i].observed, history[j].observed)
        \/ IsPrefix(history[j].observed, history[i].observed)

\* Single node: all responses (committed or not) are linearly consistent.
AllObservedConsistentInv ==
    \A i, j \in DOMAIN history :
        (history[i].type = RwTxResponse /\ history[j].type = RwTxResponse) =>
            \/ IsPrefix(history[i].observed, history[j].observed)
            \/ IsPrefix(history[j].observed, history[i].observed)

\* Observation order agrees with tx id order.
ObservedOrderMatchesTxIdInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[j].type = RwTxResponse
        /\ history[i].tx_id[2] < history[j].tx_id[2]
        => IsPrefix(history[i].observed, history[j].observed)

ExternalHistoryInv ==
    /\ AllRwReceivedIsFirstSentInv
    /\ UniqueResponseInv
    /\ UniqueTxIdsInv
    /\ ObservedOwnTxInv
    /\ CommittedHasResponseInv
    /\ AllCommittedObservedInv
    /\ AllObservedConsistentInv
    /\ ObservedOrderMatchesTxIdInv

Inv ==
    /\ TypeOK
    /\ AllTxIdsStillValidInv
    /\ NoInvalidStatusInv
    /\ ExternalHistoryInv

-----------------------------------------------------------------------------
\* Behavior

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..1 |-> <<>>]

NumRequests == Cardinality({i \in DOMAIN history : history[i].type = RwTxRequest})

NextRequestId == NumRequests + 1

CurrentView == Len(ledgerBranches)

TxInLedger(tx) ==
    \E v \in DOMAIN ledgerBranches :
        \E s \in DOMAIN ledgerBranches[v] :
            /\ "tx" \in DOMAIN ledgerBranches[v][s]
            /\ ledgerBranches[v][s].tx = tx

Responded(tx) ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx = tx

\* Txs recorded in branch v at positions 1..s, in ledger order.
ObservedTxs(v, s) ==
    LET entries == SelectSeq(SubSeq(ledgerBranches[v], 1, s),
                             LAMBDA e : "tx" \in DOMAIN e)
    IN [k \in 1..Len(entries) |-> entries[k].tx]

\* A client submits a new read-write transaction with a unique identifier.
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* A requested transaction is appended to the current ledger branch.
RwTxExecuteAction ==
    /\ Len(ledgerBranches[CurrentView]) < LedgerLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~TxInLedger(history[i].tx)
        /\ ledgerBranches' =
            [ledgerBranches EXCEPT ![CurrentView] =
                Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* The service responds with the tx id and the observed preceding txs.
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E v \in DOMAIN ledgerBranches :
        \E s \in DOMAIN ledgerBranches[v] :
            /\ "tx" \in DOMAIN ledgerBranches[v][s]
            /\ \E i \in DOMAIN history :
                /\ history[i].type = RwTxRequest
                /\ history[i].tx = ledgerBranches[v][s].tx
            /\ ~Responded(ledgerBranches[v][s].tx)
            /\ history' = Append(history,
                    [type     |-> RwTxResponse,
                     tx       |-> ledgerBranches[v][s].tx,
                     observed |-> ObservedTxs(v, s),
                     tx_id    |-> <<ledgerBranches[v][s].view, s>>])
    /\ UNCHANGED ledgerBranches

\* The service reports a transaction as committed when it is at the
\* expected position in the current ledger.
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(Last(ledgerBranches)) >= history[i].tx_id[2]
        /\ Last(ledgerBranches)[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Other, untracked transactions are appended to the ledger.
AppendOtherTxnAction ==
    /\ Len(ledgerBranches[CurrentView]) < LedgerLimit
    /\ ledgerBranches' =
        [ledgerBranches EXCEPT ![CurrentView] =
            Append(@, [view |-> CurrentView])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

StateConstraint ==
    /\ Len(history) <= HistoryLimit
    /\ \A v \in DOMAIN ledgerBranches : Len(ledgerBranches[v]) <= LedgerLimit

=============================================================================