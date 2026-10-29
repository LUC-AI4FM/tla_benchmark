---------------------------- MODULE MultiNodeLedger ----------------------------
(***************************************************************************)
(* Replicated ledger service with multiple views (leader epochs).          *)
(* ledgerBranches[v] is the ledger branch for view v. The current branch   *)
(* is ledgerBranches[view]. A view change truncates the current branch     *)
(* (never below commitSeqNum) and copies the remaining prefix into a       *)
(* strictly newer view's branch. Clients submit read/write transactions,   *)
(* get a tx id <<view, seqnum>>, and later get a status response           *)
(* (committed or invalid). All events are recorded in history.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

\* Model bounds, defined as operators so the module has no free constants
Txs      == {1, 2}
MaxView  == 3
Views    == 1 .. MaxView

\* Event types
RwTxRequest             == "RwTxRequest"
RwTxResponse            == "RwTxResponse"
TxStatusReceived        == "TxStatusReceived"
CommittedStatus         == "CommittedStatus"
InvalidStatus           == "InvalidStatus"

VARIABLES
    history,         \* sequence of client-visible events
    ledgerBranches,  \* function: view -> sequence of [view, tx] entries
    view,            \* current view
    commitSeqNum     \* authoritative commit sequence number

vars == <<history, ledgerBranches, view, commitSeqNum>>

CurrentBranch == ledgerBranches[view]

LedgerEntries == [view : Views, tx : Txs]

TxIds == Views \X (1 .. Cardinality(Txs))

Events ==
    [type : {RwTxRequest}, tx : Txs]
    \cup [type : {RwTxResponse}, tx : Txs, tx_id : TxIds]
    \cup [type : {TxStatusReceived}, tx_id : TxIds,
          status : {CommittedStatus, InvalidStatus}]

-----------------------------------------------------------------------------
(* Helpers *)

Requested(tx) == \E i \in DOMAIN history :
                    history[i].type = RwTxRequest /\ history[i].tx = tx

Responded(tx) == \E i \in DOMAIN history :
                    history[i].type = RwTxResponse /\ history[i].tx = tx

InBranch(b, tx) == \E s \in DOMAIN b : b[s].tx = tx

StatusSent(txid, st) == \E i \in DOMAIN history :
                           /\ history[i].type = TxStatusReceived
                           /\ history[i].tx_id = txid
                           /\ history[i].status = st

\* A tx id <<v, s>> is committed iff s is within the commit prefix of the
\* current branch and the entry at s was created in view v.
IsCommitted(txid) ==
    /\ txid[2] <= commitSeqNum
    /\ txid[2] \in DOMAIN CurrentBranch
    /\ CurrentBranch[txid[2]].view = txid[1]

\* A tx id <<v, s>> can never become committed.
CannotCommit(txid) ==
    \/ /\ txid[2] <= commitSeqNum
       /\ CurrentBranch[txid[2]].view # txid[1]
    \/ /\ view > txid[1]
       /\ \/ txid[2] > Len(CurrentBranch)
          \/ CurrentBranch[txid[2]].view # txid[1]

-----------------------------------------------------------------------------
TypeOK ==
    /\ history \in Seq(Events)
    /\ ledgerBranches \in [Views -> Seq(LedgerEntries)]
    /\ view \in Views
    /\ commitSeqNum \in Nat
    /\ commitSeqNum <= Len(CurrentBranch)

Init ==
    /\ history = << >>
    /\ ledgerBranches = [v \in Views |-> << >>]
    /\ view = 1
    /\ commitSeqNum = 0

-----------------------------------------------------------------------------
(* Actions *)

\* Client submits a read/write transaction
RwTxRequestAction ==
    \E tx \in Txs :
        /\ ~Requested(tx)
        /\ history' = Append(history, [type |-> RwTxRequest, tx |-> tx])
        /\ UNCHANGED <<ledgerBranches, view, commitSeqNum>>

\* Leader executes a requested transaction, appending it to its branch
RwTxExecuteAction ==
    \E tx \in Txs :
        /\ Requested(tx)
        /\ ~Responded(tx)
        /\ ~InBranch(CurrentBranch, tx)
        /\ ledgerBranches' = [ledgerBranches EXCEPT
                                ![view] = Append(@, [view |-> view, tx |-> tx])]
        /\ UNCHANGED <<history, view, commitSeqNum>>

\* Client receives the tx id <<view, seqnum>> of an executed transaction
RwTxResponseAction ==
    \E tx \in Txs, s \in DOMAIN CurrentBranch :
        /\ Requested(tx)
        /\ ~Responded(tx)
        /\ CurrentBranch[s].tx = tx
        /\ history' = Append(history,
                         [type  |-> RwTxResponse,
                          tx    |-> tx,
                          tx_id |-> <<CurrentBranch[s].view, s>>])
        /\ UNCHANGED <<ledgerBranches, view, commitSeqNum>>

\* View change: truncate uncommitted suffix and move to a newer view
TruncateLedgerAction ==
    \E newView \in Views, keep \in commitSeqNum .. Len(CurrentBranch) :
        /\ newView > view
        /\ ledgerBranches' = [ledgerBranches EXCEPT
                                ![newView] = SubSeq(CurrentBranch, 1, keep)]
        /\ view' = newView
        /\ UNCHANGED <<history, commitSeqNum>>

\* Commit advances by one entry of the current branch
IncreaseCommitSeqNumAction ==
    /\ commitSeqNum < Len(CurrentBranch)
    /\ commitSeqNum' = commitSeqNum + 1
    /\ UNCHANGED <<history, ledgerBranches, view>>

\* Reply that a transaction is committed
StatusCommittedResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ IsCommitted(history[i].tx_id)
        /\ ~StatusSent(history[i].tx_id, CommittedStatus)
        /\ history' = Append(history,
                         [type   |-> TxStatusReceived,
                          tx_id  |-> history[i].tx_id,
                          status |-> CommittedStatus])
        /\ UNCHANGED <<ledgerBranches, view, commitSeqNum>>

\* Reply that a transaction is invalid (it can never be committed)
StatusInvalidResponseAction ==
    \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ CannotCommit(history[i].tx_id)
        /\ ~StatusSent(history[i].tx_id, InvalidStatus)
        /\ history' = Append(history,
                         [type   |-> TxStatusReceived,
                          tx_id  |-> history[i].tx_id,
                          status |-> InvalidStatus])
        /\ UNCHANGED <<ledgerBranches, view, commitSeqNum>>

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ TruncateLedgerAction
    \/ IncreaseCommitSeqNumAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

Fairness ==
    /\ WF_vars(IncreaseCommitSeqNumAction)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Every committed status matches the committed view and sequence number
CommittedStatusOK ==
    \A i \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[i].status = CommittedStatus)
        => IsCommitted(history[i].tx_id)

\* Every invalid status is justified: the tx is not (and can never be) committed
InvalidStatusOK ==
    \A i \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[i].status = InvalidStatus)
        => /\ ~IsCommitted(history[i].tx_id)
           /\ CannotCommit(history[i].tx_id)

\* No transaction is reported both committed and invalid
NoConflictingStatus ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx_id = history[j].tx_id)
        => history[i].status = history[j].status

\* Every response refers to a tx recorded in some branch with that view
ResponsesRelateToLedger ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            \E v \in Views :
                /\ history[i].tx_id[2] \in DOMAIN ledgerBranches[v]
                /\ ledgerBranches[v][history[i].tx_id[2]].view = history[i].tx_id[1]

\* Committed prefix fits in the current branch
CommitWithinBranch == commitSeqNum <= Len(CurrentBranch)

SafetyInv ==
    /\ CommittedStatusOK
    /\ InvalidStatusOK
    /\ NoConflictingStatus
    /\ CommitWithinBranch

\* Truncation (and every other step) never discards committed entries
TruncationKeepsCommitted ==
    [][ /\ commitSeqNum' >= commitSeqNum
        /\ commitSeqNum <= Len(ledgerBranches'[view'])
        /\ SubSeq(ledgerBranches'[view'], 1, commitSeqNum)
             = SubSeq(CurrentBranch, 1, commitSeqNum) ]_vars

\* Views never decrease
MonotonicView == [][view' >= view]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* If there are uncommitted proposals, the commit sequence eventually
\* advances (or the proposals are rolled back by a view change).
CommitProgress ==
    \A k \in 0 .. Cardinality(Txs) :
        (commitSeqNum = k /\ Len(CurrentBranch) > k)
            ~> (commitSeqNum > k \/ Len(CurrentBranch) = k)

\* Eventually everything in the current branch is committed
EventuallyAllCommitted ==
    <>[](commitSeqNum = Len(CurrentBranch)) \/ []<>(commitSeqNum = Len(CurrentBranch))

=============================================================================