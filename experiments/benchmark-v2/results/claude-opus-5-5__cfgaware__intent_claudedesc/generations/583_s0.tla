---------------------------- MODULE MultiNode ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS HistoryLimit, ViewLimit

VARIABLES history, ledgerBranches, commitSeqNum

vars == <<history, ledgerBranches, commitSeqNum>>

\* Event types recorded in the client-observable history
RwTxRequest      == "RwTxRequest"
RwTxResponse     == "RwTxResponse"
TxStatusReceived == "TxStatusReceived"

\* Transaction statuses
CommittedStatus == "CommittedStatus"
InvalidStatus   == "InvalidStatus"

\* The current view is the number of ledger branches
CurrentView == Len(ledgerBranches)

\* The ledger branch of the current view (the current leader's log)
Branch == ledgerBranches[CurrentView]

Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>
    /\ commitSeqNum = 0

\* A client submits a new read-write transaction with a unique identifier
RwTxRequestAction ==
    /\ Len(history) < HistoryLimit
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> Len(history) + 1])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The leader of the current view executes a requested transaction
RwTxExecuteAction ==
    /\ Len(Branch) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ \A k \in DOMAIN Branch : Branch[k].tx /= history[i].tx
        /\ ledgerBranches' =
             [ledgerBranches EXCEPT ![CurrentView] =
                 Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED <<history, commitSeqNum>>

\* The leader responds to the client with the transaction id (view, seqnum)
RwTxResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E s \in DOMAIN Branch :
        /\ \A j \in DOMAIN history :
             ~(history[j].type = RwTxResponse /\ history[j].tx_id = <<Branch[s].view, s>>)
        /\ history' = Append(history,
                [type |-> RwTxResponse, tx |-> Branch[s].tx, tx_id |-> <<Branch[s].view, s>>])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* The commit point advances in the current branch
CommitAction ==
    /\ \E s \in (commitSeqNum + 1)..Len(Branch) :
        /\ Branch[s].view = CurrentView
        /\ commitSeqNum' = s
    /\ UNCHANGED <<history, ledgerBranches>>

\* Leader election: a new view begins from a prefix of the current branch that
\* contains at least all committed entries; uncommitted entries may be discarded
TruncateLedgerAction ==
    /\ CurrentView < ViewLimit
    /\ \E i \in commitSeqNum..Len(Branch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(Branch, 1, i))
    /\ UNCHANGED <<history, commitSeqNum>>

\* A client is told its transaction is committed
StatusCommittedResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ history[i].tx_id[2] <= commitSeqNum
        /\ Branch[history[i].tx_id[2]].view = history[i].tx_id[1]
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id, status |-> CommittedStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

\* A client is told its transaction is invalid
StatusInvalidResponseAction ==
    /\ Len(history) < HistoryLimit
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxResponse
        /\ LET v == history[i].tx_id[1]
               s == history[i].tx_id[2]
           IN
           \* Commit passed this seqnum but a different tx was committed there
           \/ /\ s <= commitSeqNum
              /\ Branch[s].view /= v
           \* Commit not yet reached, but the view advanced and the tx was discarded
           \/ /\ s > commitSeqNum
              /\ CurrentView > v
              /\ \/ s > Len(Branch)
                 \/ Branch[s].view /= v
           \* Transaction in the current view, beyond the commit point and no longer in the log
           \/ /\ s > commitSeqNum
              /\ CurrentView = v
              /\ s > Len(Branch)
        /\ history' = Append(history,
                [type |-> TxStatusReceived, tx_id |-> history[i].tx_id, status |-> InvalidStatus])
    /\ UNCHANGED <<ledgerBranches, commitSeqNum>>

Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ CommitAction
    \/ TruncateLedgerAction
    \/ StatusCommittedResponseAction
    \/ StatusInvalidResponseAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest}, tx : Nat]
                       \cup [type : {RwTxResponse}, tx : Nat, tx_id : Nat \X Nat]
                       \cup [type : {TxStatusReceived}, tx_id : Nat \X Nat,
                             status : {CommittedStatus, InvalidStatus}])
    /\ ledgerBranches \in Seq(Seq([view : Nat, tx : Nat]))
    /\ commitSeqNum \in Nat

\* The committed prefix is always present in the current branch
CommittedPrefixInv ==
    commitSeqNum <= Len(Branch)

\* Committed transactions are permanent across all view changes
CommittedStatusPermanentInv ==
    \A i \in DOMAIN history :
        (history[i].type = TxStatusReceived /\ history[i].status = CommittedStatus) =>
            /\ history[i].tx_id[2] <= commitSeqNum
            /\ Branch[history[i].tx_id[2]].view = history[i].tx_id[1]

\* Every branch descends from its predecessor without touching committed entries
BranchesConsistentInv ==
    \A b \in 1..(Len(ledgerBranches) - 1) :
        \A k \in 1..Len(ledgerBranches[b + 1]) :
            ledgerBranches[b + 1][k].view <= b =>
                /\ k <= Len(ledgerBranches[b])
                /\ ledgerBranches[b + 1][k] = ledgerBranches[b][k]

\* Invalid transactions are never committed, and vice versa
InvalidNotCommittedInv ==
    \A i, j \in DOMAIN history :
        (/\ history[i].type = TxStatusReceived
         /\ history[j].type = TxStatusReceived
         /\ history[i].tx_id = history[j].tx_id)
            => history[i].status = history[j].status

\* An invalid transaction can never be committed in the current state
InvalidStatusSoundInv ==
    \A i \in DOMAIN history :
        (history[i].type = TxStatusReceived /\ history[i].status = InvalidStatus) =>
            \/ history[i].tx_id[2] > Len(Branch)
            \/ Branch[history[i].tx_id[2]].view /= history[i].tx_id[1]

=============================================================================