---------------------------- MODULE MCMultiNodeBounded ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

ASSUME HistoryLimit \in Nat /\ ViewLimit \in Nat /\ ViewLimit >= 1

RwTxRequest == "RwTxRequest"
RwTxExecute == "RwTxExecute"
RwTxResponse == "RwTxResponse"
RoTxRequest == "RoTxRequest"
RoTxResponse == "RoTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"

VARIABLES history, ledgerBranches, commitIndex

vars == <<history, ledgerBranches, commitIndex>>

CurrentView == Len(ledgerBranches)
Ledger == ledgerBranches[CurrentView]

TxsOf(seq) == [k \in DOMAIN seq |-> seq[k].tx]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

NextRequestId ==
    Cardinality({i \in DOMAIN history : history[i].type \in {RwTxRequest, RoTxRequest}}) + 1

HasResponse(tx) ==
    \E j \in DOMAIN history :
        /\ history[j].type \in {RwTxResponse, RoTxResponse}
        /\ history[j].tx = tx

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitIndex = 0

RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~HasResponse(history[i].tx)
        /\ \A k \in DOMAIN Ledger : Ledger[k].tx /= history[i].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![CurrentView] =
                Append(Ledger, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitIndex>>

RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~HasResponse(history[i].tx)
        /\ \E s \in DOMAIN Ledger :
            /\ Ledger[s].tx = history[i].tx
            /\ history' = Append(history,
                    [type |-> RwTxResponse,
                     tx |-> history[i].tx,
                     observed |-> TxsOf(SubSeq(Ledger, 1, s - 1)),
                     tx_id |-> <<Ledger[s].view, s>>])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

RoTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

RoTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ Len(Ledger) > 0
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~HasResponse(history[i].tx)
        /\ history' = Append(history,
                [type |-> RoTxResponse,
                 tx |-> history[i].tx,
                 observed |-> TxsOf(Ledger),
                 tx_id |-> <<Ledger[Len(Ledger)].view, Len(Ledger)>>])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

AdvanceCommitAction ==
    /\ commitIndex < Len(Ledger)
    /\ \E c \in (commitIndex + 1)..Len(Ledger) : commitIndex' = c
    /\ UNCHANGED <<history, ledgerBranches>>

StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id[2] <= commitIndex
        /\ Ledger[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

SingleNodeActions ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction
    \/ AdvanceCommitAction
    \/ StatusCommittedResponseAction

\* View change: a new branch is created from a prefix of the current one,
\* never discarding committed entries. Bounded by ViewLimit.
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in commitIndex..Len(Ledger) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Ledger, 1, i))
    /\ UNCHANGED <<history, commitIndex>>

\* Client learns a transaction is invalid. Bounded by HistoryLimit.
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(Ledger) >= history[i].tx_id[2]
        /\ Ledger[history[i].tx_id[2]].view /= history[i].tx_id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitIndex>>

NextMultiNodeBounded ==
    \/ SingleNodeActions
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][NextMultiNodeBounded]_vars

-----------------------------------------------------------------------------
\* Helpers for invariants

RwResponses == {i \in DOMAIN history : history[i].type = RwTxResponse}

CommittedTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history :
        history[j].type = TxStatusReceived /\ history[j].status = CommittedStatus}}

InvalidTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history :
        history[j].type = TxStatusReceived /\ history[j].status = InvalidStatus}}

CommittedRwResponses == {i \in RwResponses : history[i].tx_id \in CommittedTxIds}

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : Nat]
                      \cup [type : {RwTxResponse, RoTxResponse}, tx : Nat,
                            observed : Seq(Nat), tx_id : Nat \X Nat]
                      \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                            status : {CommittedStatus, InvalidStatus}])
    /\ commitIndex \in 0..Len(Ledger)
    /\ Len(ledgerBranches) \in 1..ViewLimit

UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in {RwTxRequest, RoTxRequest}
        /\ history[j].type \in {RwTxRequest, RoTxRequest}
        /\ i /= j
        => history[i].tx /= history[j].tx

UniqueTxsInv ==
    \A i, j \in RwResponses :
        history[i].tx_id = history[j].tx_id => history[i].tx = history[j].tx

AtMostOneResponsePerTxInv ==
    \A i, j \in DOMAIN history :
        /\ history[i].type \in {RwTxResponse, RoTxResponse}
        /\ history[j].type \in {RwTxResponse, RoTxResponse}
        /\ history[i].tx = history[j].tx
        => i = j

CommittedRwSerializableInv ==
    \A i, j \in CommittedRwResponses :
        \/ IsPrefix(Append(history[i].observed, history[i].tx), history[j].observed)
        \/ IsPrefix(Append(history[j].observed, history[j].tx), history[i].observed)
        \/ i = j

CommittedRwLinearizableInv ==
    \A i, j \in DOMAIN history :
        /\ i < j
        /\ i \in CommittedRwResponses
        /\ history[j].type = RwTxRequest
        => \A k \in RwResponses :
              history[k].tx = history[j].tx =>
                 \E m \in DOMAIN history[k].observed :
                    history[k].observed[m] = history[i].tx

CommittedInLedgerInv ==
    \A tid \in CommittedTxIds :
        /\ tid[2] <= commitIndex
        /\ Ledger[tid[2]].view = tid[1]

CommittedObservedInLedgerInv ==
    \A i \in CommittedRwResponses :
        TxsOf(SubSeq(Ledger, 1, history[i].tx_id[2] - 1)) = history[i].observed

ConsistentObservationsAcrossViewsInv ==
    \A i, j \in RwResponses :
        history[i].tx_id = history[j].tx_id =>
            history[i].observed = history[j].observed

InvalidNotCommittedInv ==
    CommittedTxIds \cap InvalidTxIds = {}

InvalidNotInLedgerInv ==
    \A tid \in InvalidTxIds :
        tid[2] <= Len(Ledger) => Ledger[tid[2]].view /= tid[1]

CommitPrefixSharedInv ==
    \A v \in DOMAIN ledgerBranches :
        v >= 1 /\ commitIndex <= Len(ledgerBranches[v]) /\ v = CurrentView
        => TRUE

=============================================================================