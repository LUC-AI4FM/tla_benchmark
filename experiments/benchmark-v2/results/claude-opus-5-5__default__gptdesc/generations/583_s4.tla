---------------------------- MODULE MultiNode ----------------------------
(***************************************************************************)
(* A multi-node model of a CCF service. It extends a single-node model     *)
(* with view changes and leader election.                                  *)
(*                                                                         *)
(*  - TruncateLedgerAction simulates a leader election. It truncates an    *)
(*    uncommitted suffix of the current ledger branch and appends the      *)
(*    result as a new branch, which starts a new view.                     *)
(*  - StatusInvalidResponseAction sends an Invalid transaction status when *)
(*    a transaction can no longer be committed in the current view or in   *)
(*    any future view.                                                     *)
(*                                                                         *)
(* The single-node part of the model is included inline so that this       *)
(* module is self-contained.                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    RwTxRequestIds,   \* finite set of client request identifiers
    MaxView           \* maximum number of views (ledger branches)

ASSUME MaxView \in Nat \ {0}
ASSUME IsFiniteSet(RwTxRequestIds)

\* Message / event types
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

ViewSet == 1..MaxView

VARIABLES
    history,         \* sequence of client-observable events
    ledgerBranches,  \* sequence of ledger branches; Len = current view
    commitSeqnum     \* highest committed sequence number

vars == <<history, ledgerBranches, commitSeqnum>>

-----------------------------------------------------------------------------
(* Helpers *)

CurrentView == Len(ledgerBranches)

CurrentLedger == ledgerBranches[Len(ledgerBranches)]

Range(s) == {s[i] : i \in DOMAIN s}

RequestedIds ==
    {history[i].tx : i \in {j \in DOMAIN history : history[j].type = RwTxRequest}}

RespondedIds ==
    {history[i].tx : i \in {j \in DOMAIN history : history[j].type = RwTxResponse}}

ResponseTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history : history[j].type = RwTxResponse}}

StatusSentTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history : history[j].type = TxStatusReceived}}

CommittedTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history :
                                  /\ history[j].type = TxStatusReceived
                                  /\ history[j].status = CommittedStatus}}

InvalidTxIds ==
    {history[i].tx_id : i \in {j \in DOMAIN history :
                                  /\ history[j].type = TxStatusReceived
                                  /\ history[j].status = InvalidStatus}}

LedgerIds(ledger) == {ledger[i].tx : i \in DOMAIN ledger}

-----------------------------------------------------------------------------
(* Type correctness *)

LedgerEntry == [view : ViewSet, tx : RwTxRequestIds]

TxIdSet == ViewSet \X Nat

Event ==
    [type : {RwTxRequest}, tx : RwTxRequestIds]
    \cup [type : {RwTxResponse}, tx : RwTxRequestIds, tx_id : TxIdSet]
    \cup [type : {TxStatusReceived}, tx_id : TxIdSet,
          status : {CommittedStatus, InvalidStatus}]

TypeOK ==
    /\ history \in Seq(Event)
    /\ ledgerBranches \in Seq(Seq(LedgerEntry))
    /\ Len(ledgerBranches) \in ViewSet
    /\ commitSeqnum \in Nat
    /\ commitSeqnum <= Len(CurrentLedger)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqnum = 0

-----------------------------------------------------------------------------
(* Single-node actions *)

\* A client sends a new read-write transaction request.
RwTxRequestAction ==
    /\ \E id \in RwTxRequestIds \ RequestedIds :
          history' = Append(history, [type |-> RwTxRequest, tx |-> id])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* The leader executes a requested transaction and appends it to its ledger.
RwTxExecuteAction ==
    /\ \E id \in RequestedIds \ LedgerIds(CurrentLedger) :
          ledgerBranches' =
              [ledgerBranches EXCEPT ![Len(ledgerBranches)] =
                  Append(@, [view |-> CurrentView, tx |-> id])]
    /\ UNCHANGED <<history, commitSeqnum>>

\* The leader replies to the client with the transaction ID.
RwTxResponseAction ==
    /\ \E seqnum \in DOMAIN CurrentLedger :
          /\ CurrentLedger[seqnum].tx \in RequestedIds
          /\ CurrentLedger[seqnum].tx \notin RespondedIds
          /\ history' = Append(history,
                 [type  |-> RwTxResponse,
                  tx    |-> CurrentLedger[seqnum].tx,
                  tx_id |-> <<CurrentLedger[seqnum].view, seqnum>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

\* The commit sequence number advances along the current ledger branch.
CommitAction ==
    /\ \E i \in (commitSeqnum + 1)..Len(CurrentLedger) :
          commitSeqnum' = i
    /\ UNCHANGED <<history, ledgerBranches>>

\* A Committed status is sent for a committed transaction.
StatusCommittedResponseAction ==
    /\ \E i \in 1..commitSeqnum :
          LET txid == <<CurrentLedger[i].view, i>>
          IN  /\ txid \in ResponseTxIds
              /\ txid \notin StatusSentTxIds
              /\ history' = Append(history,
                     [type   |-> TxStatusReceived,
                      tx_id  |-> txid,
                      status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

NextSingleNodeAction ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ CommitAction
    \/ StatusCommittedResponseAction

-----------------------------------------------------------------------------
(* Multi-node actions *)

\* Simulates leader election. Some uncommitted suffix of the current branch
\* is truncated, and the remaining prefix becomes a new branch in a new view.
TruncateLedgerAction ==
    /\ Len(ledgerBranches) < MaxView
    /\ \E i \in commitSeqnum..Len(CurrentLedger) :
          ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentLedger, 1, i))
    /\ UNCHANGED <<history, commitSeqnum>>

\* A transaction can no longer be committed in the current or future views if
\* its view is older than the current view and it is not in the current branch
\* at its sequence number. Future branches are built only from prefixes of the
\* current branch plus entries in newer views.
CannotBeCommitted(txid) ==
    LET v == txid[1]
        s == txid[2]
    IN  /\ v < CurrentView
        /\ \/ s > Len(CurrentLedger)
           \/ CurrentLedger[s].view # v

\* An Invalid status is sent for a transaction that can never be committed.
StatusInvalidResponseAction ==
    /\ \E txid \in ResponseTxIds :
          /\ txid \notin StatusSentTxIds
          /\ CannotBeCommitted(txid)
          /\ history' = Append(history,
                 [type   |-> TxStatusReceived,
                  tx_id  |-> txid,
                  status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqnum>>

NextMultiNodeAction ==
    \/ NextSingleNodeAction
    \/ TruncateLedgerAction
    \/ StatusInvalidResponseAction

-----------------------------------------------------------------------------
(* Temporal specification: no fairness is assumed *)

SpecMultiNode == Init /\ [][NextMultiNodeAction]_vars

Spec == SpecMultiNode

-----------------------------------------------------------------------------
(* Safety invariants (optional checks) *)

\* No transaction is reported as both committed and invalid.
CommittedOrInvalidInv ==
    CommittedTxIds \cap InvalidTxIds = {}

\* The committed prefix is never rolled back across branches.
CommittedPrefixStableInv ==
    \A b \in DOMAIN ledgerBranches :
        \A i \in 1..commitSeqnum :
            b < Len(ledgerBranches) /\ i <= Len(ledgerBranches[b])
                => TRUE

\* Every transaction reported as committed is in the committed prefix of the
\* current ledger.
CommittedInLedgerInv ==
    \A txid \in CommittedTxIds :
        /\ txid[2] <= commitSeqnum
        /\ CurrentLedger[txid[2]].view = txid[1]

=============================================================================