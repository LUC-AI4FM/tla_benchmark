---------------------------- MODULE SingleNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Txs,        \* identifiers of client read-write transactions
    OtherTxs    \* identifiers of unrelated transactions appended to the ledger

ASSUME Txs \cap OtherTxs = {}

\* Abstract external history of requests and responses
\* Abstract per-view ledger branches; with a single node there are no view changes
VARIABLES history, ledgerBranches

vars == << history, ledgerBranches >>

\* There are no view changes, so the only view is 1
View == 1

\* Event types in the external history
RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
TxStatuses == {CommittedStatus}

\* Transaction IDs are pairs of view and sequence number
ViewSeqNums == Nat \X Nat

AllTxs == Txs \cup OtherTxs

\* Sequence s is a prefix of sequence t
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

\* Set of all finite sequences over S whose elements are distinct
DistinctSeqs(S) ==
    { s \in Seq(S) : \A i, j \in DOMAIN s : i # j => s[i] # s[j] }

-----------------------------------------------------------------------------
\* Type correctness

HistoryTypeOK ==
    \A i \in DOMAIN history :
        \/ /\ history[i].type = RwTxRequest
           /\ history[i].tx \in Txs
        \/ /\ history[i].type = RwTxResponse
           /\ history[i].tx \in Txs
           /\ history[i].observed \in Seq(AllTxs)
           /\ history[i].tx_id \in ViewSeqNums
        \/ /\ history[i].type = TxStatusReceived
           /\ history[i].tx_id \in ViewSeqNums
           /\ history[i].status \in TxStatuses

LedgerTypeOK ==
    \A view \in DOMAIN ledgerBranches :
        \A seqnum \in DOMAIN ledgerBranches[view] :
            \* Each ledger entry is a record containing a view and a tx;
            \* the ledger entry index is the sequence number
            /\ ledgerBranches[view][seqnum].view \in Nat
            /\ ledgerBranches[view][seqnum].tx \in AllTxs

TypeOK ==
    /\ HistoryTypeOK
    /\ LedgerTypeOK

\* Each ledger branch is append-only
LedgersMonoProp ==
    [][\A view \in DOMAIN ledgerBranches :
          IsPrefix(ledgerBranches[view], ledgerBranches'[view])]_ledgerBranches

-----------------------------------------------------------------------------
\* Helpers

Ledger == ledgerBranches[View]

LedgerTxs == { Ledger[i].tx : i \in DOMAIN Ledger }

RequestedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history : history[j].type = RwTxRequest } }

RespondedTxs ==
    { history[i].tx : i \in { j \in DOMAIN history : history[j].type = RwTxResponse } }

StatusReportedTxIDs ==
    { history[i].tx_id : i \in { j \in DOMAIN history : history[j].type = TxStatusReceived } }

\* Transactions observed by the transaction at ledger index i
ObservedUpTo(i) == [ k \in 1..i |-> Ledger[k].tx ]

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ history = << >>
    /\ ledgerBranches = [ v \in {View} |-> << >> ]

\* A client submits a new read-write transaction
RwTxRequestAction ==
    \E tx \in Txs \ RequestedTxs :
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
        /\ UNCHANGED ledgerBranches

\* The node executes a requested read-write transaction, appending it to the ledger
RwTxExecuteAction ==
    \E tx \in RequestedTxs \ LedgerTxs :
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![View] =
                                Append(@, [view |-> View, tx |-> tx])]
        /\ UNCHANGED history

\* The node responds to a client for an executed read-write transaction
RwTxResponseAction ==
    \E i \in DOMAIN Ledger :
        /\ Ledger[i].tx \in RequestedTxs
        /\ Ledger[i].tx \notin RespondedTxs
        /\ history' = Append(history,
                [type     |-> RwTxResponse,
                 tx       |-> Ledger[i].tx,
                 observed |-> ObservedUpTo(i),
                 tx_id    |-> << Ledger[i].view, i >>])
        /\ UNCHANGED ledgerBranches

\* The node reports that a transaction is committed. With a single node,
\* every transaction in the ledger may be committed. Only transactions whose
\* response has been sent are reported to clients.
StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id \notin StatusReportedTxIDs
        /\ history' = Append(history,
                [type   |-> TxStatusReceived,
                 tx_id  |-> history[i].tx_id,
                 status |-> CommittedStatus])
        /\ UNCHANGED ledgerBranches

\* The node appends a transaction unrelated to any tracked client request
AppendOtherTxnAction ==
    \E tx \in OtherTxs \ LedgerTxs :
        /\ ledgerBranches' = [ledgerBranches EXCEPT ![View] =
                                Append(@, [view |-> View, tx |-> tx])]
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