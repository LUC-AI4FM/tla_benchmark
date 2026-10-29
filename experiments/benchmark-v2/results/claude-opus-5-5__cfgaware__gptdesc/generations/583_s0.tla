---------------------------- MODULE MultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

\* Event types
RwTxRequest == "RwTxRequest"
RwTxResponse == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus == "InvalidStatus"

\* Helpers
Last(s) == s[Len(s)]

MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m

CurrentView == Len(ledgerBranches)

CurrentBranch == Last(ledgerBranches)

\* Highest sequence number for which a committed status has been reported.
\* This prefix must never be truncated.
CommittedSeqNum ==
    MaxOf({0} \cup
          { history[k].tx_id[2] :
              k \in { j \in DOMAIN history :
                        /\ history[j].type = TxStatusReceived
                        /\ history[j].status = CommittedStatus } })

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RwTxResponse, TxStatusReceived},
                        tx : Nat, tx_id : Nat \X Nat, status : {CommittedStatus, InvalidStatus}]
                       \cup [type : {RwTxRequest}, tx : Nat]
                       \cup [type : {RwTxResponse}, tx : Nat, tx_id : Nat \X Nat]
                       \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                             status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq([view : Nat, tx : Nat]))

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

-----------------------------------------------------------------------------
\* Single-node behaviour

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED ledgerBranches

\* The current leader executes a pending request, appending it to the ledger
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN CurrentBranch : CurrentBranch[j].tx /= history[i].tx
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* The service replies to the client with the transaction id
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E s \in DOMAIN CurrentBranch :
        /\ \A j \in DOMAIN history :
            ~ (/\ history[j].type = RwTxResponse
               /\ history[j].tx = CurrentBranch[s].tx)
        /\ history' = Append(history,
                        [type |-> RwTxResponse,
                         tx |-> CurrentBranch[s].tx,
                         tx_id |-> <<CurrentBranch[s].view, s>>])
    /\ UNCHANGED ledgerBranches

\* The service reports that a transaction is committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ Len(CurrentBranch) >= history[i].tx_id[2]
        /\ CurrentBranch[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                        [type |-> TxStatusReceived,
                         tx_id |-> history[i].tx_id,
                         status |-> CommittedStatus])
    /\ UNCHANGED ledgerBranches

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
\* Multi-node behaviour

\* Leader election: a new view starts, keeping a prefix of the latest branch
\* (at least everything reported as committed) and discarding the rest.
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in CommittedSeqNum..Len(CurrentBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, i))
    /\ UNCHANGED history

\* The service reports a transaction as invalid when it can no longer be
\* committed in the current view or any future view.
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ \/ /\ Len(CurrentBranch) >= history[i].tx_id[2]
              /\ CurrentBranch[history[i].tx_id[2]].view /= history[i].tx_id[1]
           \/ /\ Len(CurrentBranch) < history[i].tx_id[2]
              /\ history[i].tx_id[1] < CurrentView
        /\ history' = Append(history,
                        [type |-> TxStatusReceived,
                         tx_id |-> history[i].tx_id,
                         status |-> InvalidStatus])
    /\ UNCHANGED ledgerBranches

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

Next == NextMultiNodeAction

Spec == Init /\ [][NextMultiNodeAction]_vars

=============================================================================