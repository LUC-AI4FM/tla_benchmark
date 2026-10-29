---- MODULE SingleNodeReads ----
\* Expanding a single-node model (inlined here so the module is self-contained)
\* with read-only transactions.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ViewLimit, RequestLimit

ASSUME ViewLimit \in Nat \ {0}
ASSUME RequestLimit \in Nat

\* Event types recorded in the history
CONSTANTS RwTxRequest, RwTxResponse, RoTxRequest, RoTxResponse,
          TxStatusReceived, CommittedStatus, InvalidStatus

VARIABLES history, ledgerBranches

vars == << history, ledgerBranches >>

\* ---------------------------------------------------------------------------
\* Helpers inherited from the base SingleNode / external history definitions

Requests == { history[i] : i \in {j \in DOMAIN history :
                    history[j].type \in {RwTxRequest, RoTxRequest}} }

NextRequestId == Cardinality(Requests) + 1

Views == DOMAIN ledgerBranches

\* Transaction ids of a ledger branch, in order
Observed(branch) == [seqnum \in DOMAIN branch |-> branch[seqnum].tx]

\* ---------------------------------------------------------------------------
\* Base SingleNode spec

Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..1 |-> <<>>]

\* Submit a new read-write transaction
TxRequestAction ==
    /\ NextRequestId <= RequestLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction on the latest branch
TxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A view \in Views :
            \A seqnum \in DOMAIN ledgerBranches[view] :
                ledgerBranches[view][seqnum].tx # history[i].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                Append(@, [view |-> Len(ledgerBranches), tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to an executed read-write transaction
TxResponseAction ==
    /\ \E view \in Views :
        \E seqnum \in DOMAIN ledgerBranches[view] :
            /\ \A j \in DOMAIN history :
                history[j].type = RwTxResponse
                    => history[j].tx # ledgerBranches[view][seqnum].tx
            /\ history' = Append(history, [
                    type |-> RwTxResponse,
                    tx |-> ledgerBranches[view][seqnum].tx,
                    observed |-> Observed(SubSeq(ledgerBranches[view], 1, seqnum)),
                    tx_id |-> << ledgerBranches[view][seqnum].view, seqnum >> ])
    /\ UNCHANGED ledgerBranches

\* Report a transaction as committed
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(ledgerBranches[Len(ledgerBranches)]) >= history[i].tx_id[2]
        /\ ledgerBranches[Len(ledgerBranches)][history[i].tx_id[2]].view
               = history[i].tx_id[1]
        /\ history' = Append(history, [
                type |-> TxStatusReceived,
                tx_id |-> history[i].tx_id,
                status |-> CommittedStatus ])
    /\ UNCHANGED ledgerBranches

\* Start a new branch (view change), keeping a prefix of the latest branch
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in 0..Len(ledgerBranches[Len(ledgerBranches)]) :
        ledgerBranches' = Append(ledgerBranches,
                SubSeq(ledgerBranches[Len(ledgerBranches)], 1, i))
    /\ UNCHANGED history

NextSingleNodeAction ==
    \/ TxRequestAction
    \/ TxExecuteAction
    \/ TxResponseAction
    \/ StatusCommittedResponseAction
    \/ TruncateLedgerAction

\* ---------------------------------------------------------------------------
\* Read-only transaction extension

\* Submit new read-only transaction
RoTxRequestAction ==
    /\ NextRequestId <= RequestLimit
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-only transaction and respond atomically
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ \A k \in DOMAIN history :
            history[k].type = RoTxResponse => history[k].tx # history[i].tx
        /\ \E view \in Views :
            /\ Len(ledgerBranches[view]) > 0
            /\ history' = Append(history, [
                    type |-> RoTxResponse,
                    tx |-> history[i].tx,
                    observed |-> Observed(ledgerBranches[view]),
                    tx_id |-> << ledgerBranches[view][Len(ledgerBranches[view])].view,
                                 Len(ledgerBranches[view]) >> ])
    /\ UNCHANGED ledgerBranches

NextSingleNodeReadsAction ==
    \/ NextSingleNodeAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

SpecSingleNodeReads == Init /\ [][NextSingleNodeReadsAction]_vars

====