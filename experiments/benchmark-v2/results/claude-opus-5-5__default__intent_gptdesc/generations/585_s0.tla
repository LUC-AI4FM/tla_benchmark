---------------------------- MODULE SingleNodeLedgerHistory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,        \* set of client read-write transaction identifiers
    MaxViews    \* bound on the number of views (ledger branches)

ASSUME MaxViews \in Nat \ {0}
ASSUME Txs # {}

\* Event types and status values
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"

VARIABLES
    history,        \* externally visible history of events
    ledgerBranches  \* ledgerBranches[v] is the ledger a leader might produce in view v

vars == <<history, ledgerBranches>>

Views == 1..MaxViews

TxIDs == Views \X Nat

LedgerEntries == [view : Views, tx : Txs]

RequestEvents  == [type : {RwTxRequest}, tx : Txs]
ResponseEvents == [type : {RwTxResponse}, tx : Txs, observed : Seq(Txs), tx_id : TxIDs]
StatusEvents   == [type : {TxStatusReceived}, tx_id : TxIDs,
                   status : {CommittedStatus, InvalidStatus}]

Events == RequestEvents \cup ResponseEvents \cup StatusEvents

\* ---------------------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------------------

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

LastBranch == ledgerBranches[Len(ledgerBranches)]

LedgerTxs(l) == { l[k].tx : k \in DOMAIN l }

RequestedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history : history[j].type = RwTxRequest } }

RespondedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history : history[j].type = RwTxResponse } }

RespondedTxIDs ==
    { history[i].tx_id : i \in { j \in DOMAIN history : history[j].type = RwTxResponse } }

StatusTxIDs(st) ==
    { history[i].tx_id :
        i \in { j \in DOMAIN history :
                  /\ history[j].type = TxStatusReceived
                  /\ history[j].status = st } }

CommittedTxIDs == StatusTxIDs(CommittedStatus)
InvalidTxIDs   == StatusTxIDs(InvalidStatus)

\* The entry identified by tx_id exists in ledger l
InLedger(tid, l) ==
    /\ tid[2] \in 1..Len(l)
    /\ l[tid[2]].view = tid[1]

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------

Init ==
    /\ history = <<>>
    /\ ledgerBranches = <<<<>>>>

\* ---------------------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------------------

\* A client submits a new read-write transaction (identifiers are unique)
SubmitRwTx ==
    \E t \in Txs \ RequestedTxs :
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> t])
        /\ UNCHANGED ledgerBranches

\* The node executes a submitted transaction by appending it to any existing
\* ledger branch, provided it does not already appear in that branch
ExecuteRwTx ==
    \E t \in RequestedTxs, v \in DOMAIN ledgerBranches :
        /\ t \notin LedgerTxs(ledgerBranches[v])
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![v] = Append(@, [view |-> v, tx |-> t])]
        /\ UNCHANGED history

\* A new view starts; its leader's ledger is a prefix of some existing branch.
\* Committed entries must never be rolled back.
NewView ==
    /\ Len(ledgerBranches) < MaxViews
    /\ \E v \in DOMAIN ledgerBranches, k \in 0..Len(ledgerBranches[v]) :
         LET nb == SubSeq(ledgerBranches[v], 1, k) IN
         /\ \A tid \in CommittedTxIDs : InLedger(tid, nb)
         /\ ledgerBranches' = Append(ledgerBranches, nb)
    /\ UNCHANGED history

\* The node responds to a client, indicating which ledger entry executed the
\* transaction and the ledger prefix observed
RespondRwTx ==
    \E t \in RequestedTxs \ RespondedTxs, v \in DOMAIN ledgerBranches :
        LET l == ledgerBranches[v] IN
        \E s \in DOMAIN l :
            /\ l[s].tx = t
            /\ history' = Append(history,
                    [type     |-> RwTxResponse,
                     tx       |-> t,
                     observed |-> [x \in 1..s |-> l[x].tx],
                     tx_id    |-> <<l[s].view, s>>])
            /\ UNCHANGED ledgerBranches

\* The node notifies that a transaction is committed: the entry must exist
\* in the most recent branch and must not have been reported invalid
StatusCommitted ==
    \E tid \in RespondedTxIDs :
        /\ InLedger(tid, LastBranch)
        /\ tid \notin InvalidTxIDs
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> tid, status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* The node notifies that a transaction is invalid: the most recent branch
\* has a different entry at that position, and it was never reported committed
StatusInvalid ==
    \E tid \in RespondedTxIDs :
        /\ tid[2] \in 1..Len(LastBranch)
        /\ LastBranch[tid[2]].view # tid[1]
        /\ tid \notin CommittedTxIDs
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> tid, status |-> InvalidStatus])
        /\ UNCHANGED ledgerBranches

Next ==
    \/ SubmitRwTx
    \/ ExecuteRwTx
    \/ NewView
    \/ RespondRwTx
    \/ StatusCommitted
    \/ StatusInvalid

Spec == Init /\ [][Next]_vars

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

HistoryTypeOK ==
    /\ history \in Seq(Events)

LedgerTypeOK ==
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) \in 1..MaxViews
    /\ \A v \in DOMAIN ledgerBranches :
         \A k \in DOMAIN ledgerBranches[v] : ledgerBranches[v][k].view <= v

TypeOK == HistoryTypeOK /\ LedgerTypeOK

\* Each transaction identifier is requested at most once
UniqueRequestsInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxRequest
          /\ history[j].type = RwTxRequest
          /\ history[i].tx = history[j].tx ) => i = j

\* Each transaction receives at most one response
UniqueResponsesInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = RwTxResponse
          /\ history[j].type = RwTxResponse
          /\ history[i].tx = history[j].tx ) => i = j

\* No transaction is duplicated within a ledger branch
UniqueTxsInLedgerInv ==
    \A v \in DOMAIN ledgerBranches :
        \A k1, k2 \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][k1].tx = ledgerBranches[v][k2].tx => k1 = k2

\* Every response refers to a real ledger entry for that transaction
ResponsesRealInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            \E v \in DOMAIN ledgerBranches :
                /\ InLedger(history[i].tx_id, ledgerBranches[v])
                /\ ledgerBranches[v][history[i].tx_id[2]].tx = history[i].tx

\* Committed status messages refer to real entries in the most recent branch
\* and are never contradicted by an invalidation
CommittedStatusInv ==
    \A i \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = CommittedStatus ) =>
            /\ InLedger(history[i].tx_id, LastBranch)
            /\ \A j \in DOMAIN history :
                 ~ ( /\ history[j].type = TxStatusReceived
                     /\ history[j].status = InvalidStatus
                     /\ history[j].tx_id = history[i].tx_id )

Inv ==
    /\ TypeOK
    /\ UniqueRequestsInv
    /\ UniqueResponsesInv
    /\ UniqueTxsInLedgerInv
    /\ ResponsesRealInv
    /\ CommittedStatusInv

\* ---------------------------------------------------------------------------
\* Action properties (monotonicity / append-only)
\* ---------------------------------------------------------------------------

\* Ledger branches are append-only: no rollbacks, no branch removed
MonotonicLedgerProp ==
    [][ /\ Len(ledgerBranches) <= Len(ledgerBranches')
        /\ \A v \in DOMAIN ledgerBranches :
             IsPrefix(ledgerBranches[v], ledgerBranches'[v]) ]_ledgerBranches

\* The externally visible history is append-only
MonotonicHistoryProp ==
    [][ IsPrefix(history, history') ]_history

=============================================================================