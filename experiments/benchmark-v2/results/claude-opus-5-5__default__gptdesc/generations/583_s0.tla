---------------------------- MODULE MultiNode ----------------------------
(***************************************************************************)
(* Multi-node CCF service model. Extends single-node behaviour            *)
(* (request, execute, respond, commit, committed status) with view         *)
(* changes / leader election (TruncateLedgerAction) and invalid           *)
(* transaction status responses (StatusInvalidResponseAction).            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

ASSUME HistoryLimit \in Nat /\ ViewLimit \in Nat /\ ViewLimit >= 1

VARIABLES history, ledgerBranches, commitSeqNum

vars == <<history, ledgerBranches, commitSeqNum>>

\* Event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Status values
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

\* tx = 0 marks a view-change (new leader) entry rather than a client transaction
NoTx == 0

Max(a, b) == IF a > b THEN a ELSE b

Last(s) == s[Len(s)]

CurrentBranch == Last(ledgerBranches)

CurrentView == Last(CurrentBranch).view

Views == 1..ViewLimit
TxIds == 1..HistoryLimit
SeqNums == 1..(HistoryLimit + ViewLimit + 1)

LedgerEntries == [view : Views, tx : TxIds \cup {NoTx}]

TxIdPairs == Views \X Nat

Events ==
    [type : {RwTxRequest}, tx : TxIds]
    \cup [type : {RwTxResponse}, tx : TxIds, tx_id : TxIdPairs]
    \cup [type : {TxStatusReceived}, tx_id : TxIdPairs,
          status : {CommittedStatus, InvalidStatus}]

TypeOK ==
    /\ history \in Seq(Events)
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) >= 1
    /\ \A b \in DOMAIN ledgerBranches : Len(ledgerBranches[b]) >= 1
    /\ commitSeqNum \in Nat
    /\ commitSeqNum <= Len(CurrentBranch)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << << [view |-> 1, tx |-> NoTx] >> >>
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
(* Single-node behaviour *)

\* A client sends a new read-write transaction request
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The current leader executes a request, appending it to the current branch
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A j \in DOMAIN CurrentBranch : CurrentBranch[j].tx /= history[i].tx
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                  Append(CurrentBranch, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

\* The service responds to the client with the transaction id of an executed tx
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E s \in DOMAIN CurrentBranch :
        /\ CurrentBranch[s].tx /= NoTx
        /\ \A j \in DOMAIN history :
              ~(history[j].type = RwTxResponse /\ history[j].tx = CurrentBranch[s].tx)
        /\ history' = Append(history,
              [type |-> RwTxResponse,
               tx |-> CurrentBranch[s].tx,
               tx_id |-> <<CurrentBranch[s].view, s>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The commit point advances along the current branch
IncreaseCommitAction ==
    /\ \E s \in (commitSeqNum + 1)..Len(CurrentBranch) :
        commitSeqNum' = s
    /\ UNCHANGED <<history, ledgerBranches>>

\* A client learns that a transaction has been committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ s <= commitSeqNum
              /\ CurrentBranch[s].view = v
              /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> <<v, s>>,
                     status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ IncreaseCommitAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
(* Multi-node behaviour *)

\* Simulates a leader election: the uncommitted suffix of the current branch
\* is (possibly) truncated and a new branch starting in a higher view is appended.
TruncateLedgerAction ==
    /\ \E view \in (CurrentView + 1)..ViewLimit :
        \E i \in Max(commitSeqNum, 1)..Len(CurrentBranch) :
            ledgerBranches' =
                Append(ledgerBranches,
                       SubSeq(CurrentBranch, 1, i) \o << [view |-> view, tx |-> NoTx] >>)
    /\ UNCHANGED <<history, commitSeqNum>>

\* A transaction can no longer be committed in this or any future view
TxIdInvalid(v, s) ==
    \/ /\ s <= commitSeqNum
       /\ CurrentBranch[s].view /= v
    \/ \E j \in 1..commitSeqNum : CurrentBranch[j].view > v

\* Sends an INVALID status response for such a transaction
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ TxIdInvalid(v, s)
              /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> <<v, s>>,
                     status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][NextMultiNodeAction]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

\* No transaction is reported as both committed and invalid
CommittedOrInvalidInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[j].type = TxStatusReceived
          /\ history[i].tx_id = history[j].tx_id )
        => history[i].status = history[j].status

\* Committed transactions stay in the ledger at their reported position
CommittedTxsInLedgerInv ==
    \A i \in DOMAIN history :
        ( /\ history[i].type = TxStatusReceived
          /\ history[i].status = CommittedStatus )
        => /\ history[i].tx_id[2] <= Len(CurrentBranch)
           /\ CurrentBranch[history[i].tx_id[2]].view = history[i].tx_id[1]

\* Each transaction appears at most once in the current branch
UniqueTxsInv ==
    \A a, b \in DOMAIN CurrentBranch :
        (CurrentBranch[a].tx /= NoTx /\ CurrentBranch[a].tx = CurrentBranch[b].tx)
        => a = b

\* Views are monotonically non-decreasing along the current branch
MonotonicViewsInv ==
    \A a, b \in DOMAIN CurrentBranch :
        a <= b => CurrentBranch[a].view <= CurrentBranch[b].view

=============================================================================