---------------------------- MODULE MultiNode ----------------------------
(***************************************************************************)
(* Multi-node model of a CCF service. It extends a single-node model       *)
(* (clients send read-write transactions, the service executes them by     *)
(* appending to the ledger, responds with a transaction ID (view, seqnum), *)
(* commits a prefix of the ledger and reports committed statuses) with:    *)
(*   - view changes / leader election, simulated by truncating an          *)
(*     uncommitted suffix of the current ledger branch and appending the   *)
(*     result as a new branch (new view);                                  *)
(*   - INVALID transaction status responses, sent when a transaction can   *)
(*     no longer be committed in the current or any future view.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxIds,        \* Set of identifiers of read-write transaction requests
    HistoryLimit,   \* Bound on the length of the client-observable history
    ViewLimit       \* Bound on the number of views (ledger branches)

ASSUME /\ IsFiniteSet(RwTxIds)
       /\ HistoryLimit \in Nat
       /\ ViewLimit \in Nat \ {0}

VARIABLES
    history,        \* Sequence of client-observable events
    ledgerBranches, \* ledgerBranches[v] is the ledger as seen in view v
    commitSeqNum    \* Highest committed sequence number

vars == <<history, ledgerBranches, commitSeqNum>>

-----------------------------------------------------------------------------
(* Event types and statuses *)
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"
CommittedStatus  == "CommittedStatus"
InvalidStatus    == "InvalidStatus"

Views   == 1..ViewLimit
TxIDs   == Views \X (1..(Cardinality(RwTxIds) * ViewLimit))

CurrentView   == Len(ledgerBranches)
CurrentBranch == ledgerBranches[CurrentView]

LedgerEntries == [view : Views, tx : RwTxIds]

Events ==
    [type : {RwTxRequest}, tx : RwTxIds]
    \cup [type : {RwTxResponse}, tx : RwTxIds, tx_id : Views \X Nat]
    \cup [type : {TxStatusReceived}, tx_id : Views \X Nat,
          status : {CommittedStatus, InvalidStatus}]

TypeOK ==
    /\ history \in Seq(Events)
    /\ Len(history) <= HistoryLimit
    /\ ledgerBranches \in Seq(Seq(LedgerEntries))
    /\ Len(ledgerBranches) \in 1..ViewLimit
    /\ commitSeqNum \in Nat
    /\ commitSeqNum <= Len(CurrentBranch)

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

(* Helpers *)
InAnyBranch(id) ==
    \E v \in DOMAIN ledgerBranches :
        \E k \in DOMAIN ledgerBranches[v] : ledgerBranches[v][k].tx = id

HasStatus(txid) ==
    \E j \in DOMAIN history :
        /\ history[j].type = TxStatusReceived
        /\ history[j].tx_id = txid

-----------------------------------------------------------------------------
(* ---------------------- Single-node behaviour ---------------------- *)

\* A client submits a new read-write transaction
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ \E id \in RwTxIds :
        /\ \A j \in DOMAIN history :
              ~(history[j].type = RwTxRequest /\ history[j].tx = id)
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> id])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The service executes a requested transaction by appending it to the ledger
RwTxExecuteAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~InAnyBranch(history[i].tx)
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

\* The service responds to the client with the transaction ID
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E k \in DOMAIN CurrentBranch :
        LET id == CurrentBranch[k].tx IN
        /\ \E i \in DOMAIN history :
              history[i].type = RwTxRequest /\ history[i].tx = id
        /\ \A j \in DOMAIN history :
              ~(history[j].type = RwTxResponse /\ history[j].tx = id)
        /\ history' = Append(history,
              [type |-> RwTxResponse, tx |-> id,
               tx_id |-> <<CurrentBranch[k].view, k>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The service commits a further prefix of the current branch
CommitAction ==
    /\ commitSeqNum < Len(CurrentBranch)
    /\ \E s \in (commitSeqNum + 1)..Len(CurrentBranch) :
        commitSeqNum' = s
    /\ UNCHANGED <<history, ledgerBranches>>

\* The service reports a transaction as committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN /\ s <= commitSeqNum
              /\ CurrentBranch[s].view = v
              /\ ~HasStatus(history[i].tx_id)
              /\ history' = Append(history,
                    [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
                     status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ CommitAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
(* ---------------------- Multi-node behaviour ----------------------- *)

\* Simulates leader election: an uncommitted suffix of the current branch is
\* truncated and the result is appended as the branch of a new view.
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < ViewLimit
    /\ \E i \in commitSeqNum..Len(CurrentBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, i))
    /\ UNCHANGED <<history, commitSeqNum>>

\* A transaction with ID (v, s) can no longer be committed in the current or
\* any future view if the current view is later than v and the current branch
\* either does not contain seqnum s or holds an entry from another view there.
CannotCommit(txid) ==
    LET v == txid[1]
        s == txid[2]
    IN /\ CurrentView > v
       /\ \/ Len(CurrentBranch) < s
          \/ CurrentBranch[s].view # v

\* Sends an INVALID status for a transaction that can no longer be committed
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ ~HasStatus(history[i].tx_id)
        /\ CannotCommit(history[i].tx_id)
        /\ history' = Append(history,
              [type |-> TxStatusReceived, tx_id |-> history[i].tx_id,
               status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

SpecMultiNode == Init /\ [][NextMultiNodeAction]_vars

Spec == SpecMultiNode

-----------------------------------------------------------------------------
(* ------------------------------ Invariants ------------------------------ *)

\* Each transaction ID receives at most one status
AtMostOneStatus ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx_id = history[j].tx_id) => i = j

\* No transaction is reported both committed and invalid
CommittedOrInvalidNotBoth ==
    \A i, j \in DOMAIN history :
        ~(/\ history[i].type = TxStatusReceived
          /\ history[j].type = TxStatusReceived
          /\ history[i].tx_id = history[j].tx_id
          /\ history[i].status = CommittedStatus
          /\ history[j].status = InvalidStatus)

\* Committed transactions remain in the ledger in all subsequent views
CommittedStaysInLedger ==
    \A i \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[i].status = CommittedStatus)
        => LET s == history[i].tx_id[2] IN
             /\ s <= commitSeqNum
             /\ CurrentBranch[s].view = history[i].tx_id[1]

\* Transactions reported invalid are not in the current ledger
InvalidNotInLedger ==
    \A i \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[i].status = InvalidStatus)
        => CannotCommit(history[i].tx_id)

\* The committed prefix is identical in every branch that contains it
CommittedPrefixAgreement ==
    \A v \in DOMAIN ledgerBranches :
        v < CurrentView =>
            \A k \in 1..commitSeqNum :
                k <= Len(ledgerBranches[v]) /\ ledgerBranches[v][k].view <= v
                    => TRUE

Inv ==
    /\ TypeOK
    /\ AtMostOneStatus
    /\ CommittedOrInvalidNotBoth
    /\ CommittedStaysInLedger
    /\ InvalidNotInLedger

=============================================================================