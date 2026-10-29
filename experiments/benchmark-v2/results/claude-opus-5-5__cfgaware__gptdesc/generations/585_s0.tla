---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Message/event types in the abstract external history
RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"

\* Only a single node is considered, so there are no view changes.
\* The only view is the first one.
FirstView == 1
Views == {FirstView}

\* Bounds that keep the state space finite for model checking
MaxRwRequests == 3
MaxOtherTxs == 1

\* Abstract client transaction identifiers (request ids)
Txs == 1..MaxRwRequests

\* Transaction ids as observed by clients: <<view, seqnum>>
TxIDs == Views \X (1..(MaxRwRequests + MaxOtherTxs))

\* Abstract history of all client requests and responses
VARIABLE history

\* Abstract per-view ledger branches containing only transactions
\* (no signatures). With a single node there is exactly one branch.
VARIABLE ledgerBranches

vars == <<history, ledgerBranches>>

-----------------------------------------------------------------------------
\* Helpers

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

LedgerEntries ==
    [view : Views, tx : Txs] \cup [view : Views]

HistoryEntries ==
    [type : {RwTxRequest}, tx : Txs]
    \cup
    [type : {RwTxResponse}, tx : Txs, observed : Seq(Txs), tx_id : TxIDs]
    \cup
    [type : {TxStatusReceived}, tx_id : TxIDs, status : {CommittedStatus}]

IsClientTx(e) == "tx" \in DOMAIN e

\* Number of read-write requests submitted so far
NumRequests ==
    Cardinality({i \in DOMAIN history : history[i].type = RwTxRequest})

NextRequestId == NumRequests + 1

\* Number of unrelated (non-client) transactions in a branch
NumOtherTxs(view) ==
    Cardinality({s \in DOMAIN ledgerBranches[view] :
                    ~IsClientTx(ledgerBranches[view][s])})

\* Transactions that have been included in some ledger branch
ExecutedTxs ==
    {ledgerBranches[v][s].tx :
        v \in DOMAIN ledgerBranches,
        s \in {k \in DOMAIN ledgerBranches[v] : IsClientTx(ledgerBranches[v][k])}}

\* Transactions that have already been responded to
RespondedTxs ==
    {history[j].tx : j \in {k \in DOMAIN history : history[k].type = RwTxResponse}}

\* Transaction ids whose committed status has already been reported
ReportedTxIDs ==
    {history[j].tx_id : j \in {k \in DOMAIN history : history[k].type = TxStatusReceived}}

\* Client transactions observed in a ledger prefix
ObservedTxs(view, seqnum) ==
    LET prefix == SubSeq(ledgerBranches[view], 1, seqnum)
        clientOnly == SelectSeq(prefix, IsClientTx)
    IN [k \in DOMAIN clientOnly |-> clientOnly[k].tx]

-----------------------------------------------------------------------------
\* Type correctness

HistoryTypeOK ==
    /\ history \in Seq(HistoryEntries)

LedgerTypeOK ==
    /\ DOMAIN ledgerBranches = Views
    /\ \A v \in Views : ledgerBranches[v] \in Seq(LedgerEntries)

TypeOK ==
    /\ HistoryTypeOK
    /\ LedgerTypeOK

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [v \in Views |-> <<>>]

-----------------------------------------------------------------------------
\* Actions

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ NumRequests < MaxRwRequests
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* The service executes a received read-write transaction, appending it
\* to a ledger branch
RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        \* Transaction has not already been added to a ledger
        /\ history[i].tx \notin ExecutedTxs
        /\ \E view \in DOMAIN ledgerBranches :
            ledgerBranches' =
                [ledgerBranches EXCEPT
                    ![view] = Append(@, [view |-> view, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* The service responds to an executed read-write transaction
RwTxResponseAction ==
    /\ \E view \in DOMAIN ledgerBranches :
        \E seqnum \in DOMAIN ledgerBranches[view] :
            /\ IsClientTx(ledgerBranches[view][seqnum])
            /\ ledgerBranches[view][seqnum].tx \notin RespondedTxs
            /\ history' = Append(history,
                    [type     |-> RwTxResponse,
                     tx       |-> ledgerBranches[view][seqnum].tx,
                     observed |-> ObservedTxs(view, seqnum),
                     tx_id    |-> <<ledgerBranches[view][seqnum].view, seqnum>>])
    /\ UNCHANGED ledgerBranches

\* The service reports that a responded transaction is committed.
\* With a single node, every transaction in the ledger is committed.
StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id \notin ReportedTxIDs
        /\ LET view == history[i].tx_id[1]
               seqnum == history[i].tx_id[2]
           IN /\ view \in DOMAIN ledgerBranches
              /\ Len(ledgerBranches[view]) >= seqnum
              /\ ledgerBranches[view][seqnum].view = view
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* The service appends an unrelated transaction (e.g. from another client)
AppendOtherTxnAction ==
    /\ \E view \in DOMAIN ledgerBranches :
        /\ NumOtherTxs(view) < MaxOtherTxs
        /\ ledgerBranches' =
            [ledgerBranches EXCEPT ![view] = Append(@, [view |-> view])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Properties

\* Ledger branches are append-only
AppendOnlyProp ==
    [][\A view \in DOMAIN ledgerBranches :
          IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

\* History is append-only
HistoryAppendOnlyProp ==
    [][IsPrefix(history, history')]_history

=============================================================================