---------------------------- MODULE SingleNode ----------------------------
(***************************************************************************)
(* Externally visible behaviour of a single-node CCF service.             *)
(* We track an abstract external history of client requests/responses     *)
(* and abstract per-view ledger branches. Since only a single node is     *)
(* considered, there are no view changes: only view 1 exists.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES
    history,         \* external history of events observed by clients
    ledgerBranches   \* abstract ledgers, indexed by view

vars == << history, ledgerBranches >>

-----------------------------------------------------------------------------
(* External history definitions *)

\* Event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"
TxStatuses      == {CommittedStatus, InvalidStatus}

\* Single node, hence a single view
Views == {1}

\* Transaction identifiers
Txs == Nat

\* Sequence numbers
SeqNums == Nat

\* A transaction id is a pair of view and sequence number
TxIDs == Views \X SeqNums

\* Fresh identifier for the next request
NextRequestId ==
    Cardinality({i \in DOMAIN history : history[i].type = RwTxRequest})

HistoryTypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RwTxResponse, TxStatusReceived}]
                       \cup [type : {RwTxRequest}, tx : Txs]
                       \cup [type : {RwTxResponse}, tx : Txs,
                             observed : Seq(Txs), tx_id : TxIDs]
                       \cup [type : {TxStatusReceived}, tx_id : TxIDs,
                             status : TxStatuses])
    /\ \A i \in DOMAIN history :
         \/ /\ history[i].type = RwTxRequest
            /\ history[i].tx \in Txs
         \/ /\ history[i].type = RwTxResponse
            /\ history[i].tx \in Txs
            /\ history[i].observed \in Seq(Txs)
            /\ history[i].tx_id \in TxIDs
         \/ /\ history[i].type = TxStatusReceived
            /\ history[i].tx_id \in TxIDs
            /\ history[i].status \in TxStatuses

-----------------------------------------------------------------------------
(* Ledger definitions *)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

LedgerTypeOK ==
    /\ DOMAIN ledgerBranches \subseteq Views
    /\ \A view \in DOMAIN ledgerBranches :
        \A seqnum \in DOMAIN ledgerBranches[view] :
            \* Each ledger entry contains a view and optionally a tx
            /\ ledgerBranches[view][seqnum].view \in Views
            /\ "tx" \in DOMAIN ledgerBranches[view][seqnum]
                 => ledgerBranches[view][seqnum].tx \in Txs

\* Each ledger is append-only
LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches :
          IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

TypeOK ==
    /\ HistoryTypeOK
    /\ LedgerTypeOK

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = [x \in 1..1 |-> <<>>]

\* Submit a new read-write transaction
RwTxRequestAction ==
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a read-write transaction
RwTxExecuteAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        \* Transaction must not already be in a ledger
        /\ \A view \in DOMAIN ledgerBranches :
             \A seqnum \in DOMAIN ledgerBranches[view] :
                 "tx" \in DOMAIN ledgerBranches[view][seqnum]
                   => history[i].tx /= ledgerBranches[view][seqnum].tx
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![1] =
                                 Append(@, [view |-> 1, tx |-> history[i].tx])]
        /\ UNCHANGED history

\* Respond to a read-write transaction
RwTxResponseAction ==
    /\ \E i \in DOMAIN ledgerBranches[1] :
        /\ "tx" \in DOMAIN ledgerBranches[1][i]
        \* Transaction must not already have been responded to
        /\ \A j \in DOMAIN history :
             history[j].type = RwTxResponse
               => history[j].tx /= ledgerBranches[1][i].tx
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> ledgerBranches[1][i].tx,
               observed |-> SelectSeq(
                              [k \in 1..i |->
                                 IF "tx" \in DOMAIN ledgerBranches[1][k]
                                 THEN ledgerBranches[1][k].tx ELSE -1],
                              LAMBDA t : t \in Txs),
               tx_id    |-> <<ledgerBranches[1][i].view, i>>])
    /\ UNCHANGED ledgerBranches

\* Report committed status of a transaction
\* (with a single node, transactions in the ledger are committed)
StatusCommittedResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(ledgerBranches[1]) >= history[i].tx_id[2]
        /\ history' = Append(history,
              [type   |-> TxStatusReceived,
               tx_id  |-> history[i].tx_id,
               status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

\* Append a transaction that does not affect the state under consideration
AppendOtherTxnAction ==
    /\ ledgerBranches' = [ledgerBranches EXCEPT ![1] = Append(@, [view |-> 1])]
    /\ UNCHANGED history

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction
    \/ AppendOtherTxnAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => LedgersMonoProp
=============================================================================