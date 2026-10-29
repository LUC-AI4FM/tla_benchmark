---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Fixed model bounds, defined as operators so that no CONSTANT bindings are required.
Txs          == {"t1", "t2"}
MaxViews     == 2
MaxLedgerLen == 3
HistoryBound == 8

Views    == 1..MaxViews
SeqNums  == 1..MaxLedgerLen
TxIDs    == Views \X SeqNums

\* Event type tags
RwTxRequest       == "RwTxRequest"
RwTxResponse      == "RwTxResponse"
TxStatusReceived  == "TxStatusReceived"
CommittedStatus   == "CommittedStatus"
InvalidStatus     == "InvalidStatus"

VARIABLES
    \* Externally visible history of requests, responses and status messages
    history,
    \* Sequence of ledgers, indexed by view; each ledger is a sequence of
    \* entries [view |-> v, tx |-> t]
    ledgerBranches

vars == <<history, ledgerBranches>>

------------------------------------------------------------------------------
\* Helpers

Range(s) == {s[i] : i \in DOMAIN s}

LedgerTxs(l) == {l[i].tx : i \in DOMAIN l}

LastView == Len(ledgerBranches)

IsPrefix(a, b) ==
    /\ Len(a) <= Len(b)
    /\ \A i \in DOMAIN a : a[i] = b[i]

ObservedTxs(l, n) == [i \in 1..n |-> l[i].tx]

LedgerEntries == [view : Views, tx : Txs]

IsLedger(l) ==
    /\ l \in Seq(LedgerEntries)
    /\ Len(l) <= MaxLedgerLen

RequestEvents  == [type : {RwTxRequest}, tx : Txs]

IsResponseEvent(e) ==
    /\ DOMAIN e = {"type", "tx", "observed", "tx_id"}
    /\ e.type = RwTxResponse
    /\ e.tx \in Txs
    /\ e.tx_id \in TxIDs
    /\ e.observed \in Seq(Txs)
    /\ Len(e.observed) <= MaxLedgerLen

StatusEvents == [type : {TxStatusReceived},
                 tx_id : TxIDs,
                 status : {CommittedStatus, InvalidStatus}]

IsEvent(e) == e \in RequestEvents \/ IsResponseEvent(e) \/ e \in StatusEvents

------------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

------------------------------------------------------------------------------
\* Actions

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryBound
    /\ \E tx \in Txs :
        /\ \A i \in DOMAIN history :
              history[i].type = RwTxRequest => history[i].tx # tx
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
    /\ UNCHANGED ledgerBranches

\* The node executes a submitted transaction by appending it to an existing branch
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \E view \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[view]) < MaxLedgerLen
            \* no duplicates of a transaction within a ledger
            /\ history[i].tx \notin LedgerTxs(ledgerBranches[view])
            /\ ledgerBranches' =
                 [ledgerBranches EXCEPT ![view] =
                     Append(@, [view |-> view, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* A new leader (new view) starts a branch from a prefix of the latest ledger
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < MaxViews
    /\ \E n \in 0..Len(ledgerBranches[LastView]) :
        ledgerBranches' = Append(ledgerBranches,
                                 SubSeq(ledgerBranches[LastView], 1, n))
    /\ UNCHANGED history

\* The node responds to a client, indicating the executing entry and the observed prefix
RwTxResponseAction ==
    /\ Len(history) < HistoryBound
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN history :
              history[j].type = RwTxResponse => history[j].tx # history[i].tx
        /\ \E view \in DOMAIN ledgerBranches :
            \E seqnum \in DOMAIN ledgerBranches[view] :
                /\ ledgerBranches[view][seqnum].tx = history[i].tx
                /\ history' = Append(history,
                     [type     |-> RwTxResponse,
                      tx       |-> history[i].tx,
                      observed |-> ObservedTxs(ledgerBranches[view], seqnum),
                      tx_id    |-> <<ledgerBranches[view][seqnum].view, seqnum>>])
    /\ UNCHANGED ledgerBranches

\* The node notifies that a transaction is committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryBound
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET view   == history[i].tx_id[1]
               seqnum == history[i].tx_id[2]
           IN
           /\ seqnum \in DOMAIN ledgerBranches[LastView]
           /\ ledgerBranches[LastView][seqnum].view = view
           /\ \A j \in DOMAIN history :
                 ~ /\ history[j].type = TxStatusReceived
                   /\ history[j].tx_id = history[i].tx_id
           /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* The node notifies that a transaction is invalid (not in the latest branch)
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryBound
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET view   == history[i].tx_id[1]
               seqnum == history[i].tx_id[2]
           IN
           /\ view < LastView
           /\ \/ seqnum \notin DOMAIN ledgerBranches[LastView]
              \/ ledgerBranches[LastView][seqnum].view # view
           /\ \A j \in DOMAIN history :
                 ~ /\ history[j].type = TxStatusReceived
                   /\ history[j].tx_id = history[i].tx_id
           /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ TruncateLedgerAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][Next]_vars

------------------------------------------------------------------------------
\* Invariants

HistoryTypeOK ==
    /\ history \in Seq(UNION {RequestEvents, StatusEvents} \cup
                       {e \in Range(history) : IsResponseEvent(e)})
    /\ \A i \in DOMAIN history : IsEvent(history[i])

LedgerTypeOK ==
    /\ Len(ledgerBranches) >= 1
    /\ Len(ledgerBranches) <= MaxViews
    /\ \A v \in DOMAIN ledgerBranches : IsLedger(ledgerBranches[v])

TypeOK == HistoryTypeOK /\ LedgerTypeOK

\* Each transaction appears at most once in every ledger
UniqueTxsInLedgersInv ==
    \A v \in DOMAIN ledgerBranches :
        \A i, j \in DOMAIN ledgerBranches[v] :
            ledgerBranches[v][i].tx = ledgerBranches[v][j].tx => i = j

\* Each transaction is requested at most once
UniqueTxRequestsInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxRequest
         /\ history[j].type = RwTxRequest
         /\ history[i].tx = history[j].tx) => i = j

\* Each transaction is responded to at most once
UniqueTxResponsesInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = RwTxResponse
         /\ history[j].type = RwTxResponse
         /\ history[i].tx = history[j].tx) => i = j

\* Committed status messages refer to real entries in the latest branch
\* and are never contradicted by an invalidation
CommittedStatusInv ==
    \A i \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[i].status = CommittedStatus) =>
            /\ \E j \in DOMAIN history :
                  /\ history[j].type = RwTxResponse
                  /\ history[j].tx_id = history[i].tx_id
            /\ \A k \in DOMAIN history :
                  ~ /\ history[k].type = TxStatusReceived
                    /\ history[k].status = InvalidStatus
                    /\ history[k].tx_id = history[i].tx_id

\* Ledgers are append-only (action property)
LedgersMonotonicProp ==
    [][ /\ Len(ledgerBranches) <= Len(ledgerBranches')
        /\ \A v \in DOMAIN ledgerBranches :
              IsPrefix(ledgerBranches[v], ledgerBranches'[v]) ]_vars

\* History is append-only (action property)
HistoryMonotonicProp ==
    [][IsPrefix(history, history')]_vars

=============================================================================